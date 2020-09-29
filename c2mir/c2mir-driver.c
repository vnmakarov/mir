#include <string.h>
#include <stdlib.h>
#include <stdint.h>

#ifndef _WIN32
#include <dlfcn.h>
#if defined(__unix__) || defined(__APPLE__)
#include <sys/stat.h>
#endif
#else
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#endif

#include "c2mir.h"
#include "mir-gen.h"
#include "real-time.h"

struct lib {
  char *name;
  void *handler;
};

typedef struct lib lib_t;

#if defined(__unix__)
#if UINTPTR_MAX == 0xffffffff
static lib_t std_libs[] = {{"/lib/libc.so.6", NULL},
                           {"/lib32/libc.so.6", NULL},
                           {"/lib/libm.so.6", NULL},
                           {"/lib32/libm.so.6", NULL}};
static const char *std_lib_dirs[] = {"/lib", "/lib32"};
#elif UINTPTR_MAX == 0xffffffffffffffff
#if defined(__x86_64__)
static lib_t std_libs[] = {{"/lib64/libc.so.6", NULL},
                           {"/lib/x86_64-linux-gnu/libc.so.6", NULL},
                           {"/lib64/libm.so.6", NULL},
                           {"/lib/x86_64-linux-gnu/libm.so.6", NULL}};
static const char *std_lib_dirs[] = {"/lib64", "/lib/x86_64-linux-gnu"};
#elif (__aarch64__)
static lib_t std_libs[] = {{"/lib64/libc.so.6", NULL},
                           {"/lib/aarch64-linux-gnu/libc.so.6", NULL},
                           {"/lib64/libm.so.6", NULL},
                           {"/lib/aarch64-linux-gnu/libm.so.6", NULL}};
static const char *std_lib_dirs[] = {"/lib64", "/lib/aarch64-linux-gnu"};
#elif (__PPC64__)
static lib_t std_libs[] = {{"/lib64/libc.so.6", NULL},
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
                           {"/lib/powerpc64le-linux-gnu/libc.so.6", NULL},
#else
                           {"/lib/powerpc64-linux-gnu/libc.so.6", NULL},
#endif
                           {"/lib64/libm.so.6", NULL},
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
                           {"/lib/powerpc64le-linux-gnu/libm.so.6", NULL},
#else
                           {"/lib/powerpc64-linux-gnu/libm.so.6", NULL},
#endif
};
static const char *std_lib_dirs[] = {"/lib64",
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
				     "/lib/powerpc64le-linux-gnu",
#else
				     "/lib/powerpc64-linux-gnu",
#endif
};
#elif (__s390x__)
static lib_t std_libs[] = {{"/lib64/libc.so.6", NULL},
                           {"/lib/s390x-linux-gnu/libc.so.6", NULL},
                           {"/lib64/libm.so.6", NULL},
                           {"/lib/s390x-linux-gnu/libm.so.6", NULL}};
static const char *std_lib_dirs[] = {"/lib64", "/lib/s390x-linux-gnu"};
#else
#error cannot recognize 32- or 64-bit target
#endif
#endif
static const char *lib_suffix = ".so";
#endif

#ifdef _WIN32
static const int slash = '\\';
#else
static const int slash = '/';
#endif

#if defined(__APPLE__)
static lib_t std_libs[] = {{"/usr/lib/libc.dylib", NULL}, {"/usr/lib/libm.dylib", NULL}};
static const char *std_lib_dirs[] = {"/usr/lib"};
static const char *lib_suffix = ".dylib";
#endif

#ifdef _WIN32
static lib_t std_libs[] = {{"msvcrt.dll", NULL}, {"kernel32.dll", NULL}};
static const char *std_lib_dirs[] = {""};
static const char *lib_suffix = ".dll";
#define dlopen(n, f) LoadLibrary(n)
#define dlclose(h) FreeLibrary(h)
#define dlsym(h, s) GetProcAddress(h, s)
#endif

static struct c2mir_options options;
static int gen_debug_p;

static size_t curr_char, code_len;
static const uint8_t *code;

typedef void *void_ptr_t;

DEF_VARR (void_ptr_t);
static VARR (void_ptr_t) * allocated;

static void *reg_malloc (size_t s) {
  void *res = malloc (s);

  if (res == NULL) {
    fprintf (stderr, "c2m: no memory\n");
    exit (1);
  }
  VARR_PUSH (void_ptr_t, allocated, res);
  return res;
}

DEF_VARR (char);
static VARR (char) * temp_string;

typedef const char *char_ptr_t;

DEF_VARR (char_ptr_t);
static VARR (char_ptr_t) * headers;

DEF_VARR (uint8_t);

static VARR (uint8_t) * input;
static int interp_exec_p, gen_exec_p, lazy_gen_exec_p;
static VARR (char_ptr_t) * exec_argv;
static VARR (char_ptr_t) * source_file_names;

typedef struct c2mir_macro_command macro_command_t;

DEF_VARR (macro_command_t);
static VARR (macro_command_t) * macro_commands;

static void close_std_libs (void) {
  for (int i = 0; i < sizeof (std_libs) / sizeof (lib_t); i++)
    if (std_libs[i].handler != NULL) dlclose (std_libs[i].handler);
}

static void open_std_libs (void) {
  for (int i = 0; i < sizeof (std_libs) / sizeof (struct lib); i++)
    std_libs[i].handler = dlopen (std_libs[i].name, RTLD_LAZY);
}

DEF_VARR (lib_t);
static VARR (lib_t) * cmdline_libs;
static VARR (char_ptr_t) * lib_dirs;

static void *open_lib (const char *dir, const char *name) {
  const char *last_slash = strrchr (dir, slash);

  VARR_TRUNC (char, temp_string, 0);
  VARR_PUSH_ARR (char, temp_string, dir, strlen (dir));
  if (last_slash[1] != '\0') VARR_PUSH (char, temp_string, slash);
  VARR_PUSH_ARR (char, temp_string, "lib", 3);
  VARR_PUSH_ARR (char, temp_string, name, strlen (name));
  VARR_PUSH_ARR (char, temp_string, lib_suffix, strlen (lib_suffix));
  VARR_PUSH (char, temp_string, 0);
  return dlopen (VARR_ADDR (char, temp_string), RTLD_LAZY);
}

static void process_cmdline_lib (char *lib_name) {
  lib_t lib;

  lib.name = lib_name;
  for (size_t i = 0; i < VARR_LENGTH (char_ptr_t, lib_dirs); i++)
    if ((lib.handler = open_lib (VARR_GET (char_ptr_t, lib_dirs, i), lib_name)) != NULL) break;
  if (lib.handler == NULL) {
    fprintf (stderr, "cannot find library lib%s -- good bye\n", lib_name);
    exit (1);
  }
  VARR_PUSH (lib_t, cmdline_libs, lib);
}

static void close_cmdline_libs (void) {
  void *handler;

  for (size_t i = 0; i < VARR_LENGTH (lib_t, cmdline_libs); i++)
    if ((handler = VARR_GET (lib_t, cmdline_libs, i).handler) != NULL) dlclose (handler);
}

static int optimize_level;

static void init_options (int argc, char *argv[]) {
  int incl_p, ldir_p = FALSE; /* to remove an uninitialized warning */

  options.message_file = stderr;
  options.debug_p = options.verbose_p = options.asm_p = options.object_p = FALSE;
  options.output_file_name = NULL;
  options.no_prepro_p = options.prepro_only_p = options.syntax_only_p = options.pedantic_p = FALSE;
  gen_debug_p = FALSE;
  VARR_CREATE (char, temp_string, 0);
  VARR_CREATE (char_ptr_t, headers, 0);
  VARR_CREATE (macro_command_t, macro_commands, 0);
  optimize_level = -1;
  for (int i = 1; i < argc; i++) {
    if (strcmp (argv[i], "-d") == 0) {
      options.verbose_p = options.debug_p = TRUE;
    } else if (strcmp (argv[i], "-dg") == 0) {
      gen_debug_p = TRUE;
    } else if (strcmp (argv[i], "-S") == 0) {
      options.asm_p = TRUE;
    } else if (strcmp (argv[i], "-c") == 0) {
      options.object_p = TRUE;
    } else if (strcmp (argv[i], "-v") == 0) {
      options.verbose_p = TRUE;
    } else if (strcmp (argv[i], "-E") == 0) {
      options.prepro_only_p = TRUE;
    } else if (strcmp (argv[i], "-fsyntax-only") == 0) {
      options.syntax_only_p = TRUE;
    } else if (strcmp (argv[i], "-fpreprocessed") == 0) {
      options.no_prepro_p = TRUE;
    } else if (strcmp (argv[i], "-pedantic") == 0) {
      options.pedantic_p = TRUE;
    } else if (strncmp (argv[i], "-O", 2) == 0) {
      optimize_level = argv[i][2] != '\0' ? atoi (&argv[i][2]) : 2;
    } else if (strcmp (argv[i], "-o") == 0) {
      if (i + 1 >= argc)
        fprintf (stderr, "-o without argument\n");
      else
        options.output_file_name = argv[++i];
    } else if ((incl_p = strncmp (argv[i], "-I", 2) == 0)
               || (ldir_p = strncmp (argv[i], "-L", 2) == 0) || strncmp (argv[i], "-l", 2) == 0) {
      char *arg;
      const char *dir = strlen (argv[i]) == 2 && i + 1 < argc ? argv[++i] : argv[i] + 2;

      if (*dir == '\0') continue;
      arg = reg_malloc (strlen (dir) + 1);
      strcpy (arg, dir);
      if (incl_p || ldir_p)
        VARR_PUSH (char_ptr_t, incl_p ? headers : lib_dirs, arg);
      else
        process_cmdline_lib (arg);
    } else if (strncmp (argv[i], "-U", 2) == 0 || strncmp (argv[i], "-D", 2) == 0) {
      char *str;
      const char *bound, *def = strlen (argv[i]) == 2 && i + 1 < argc ? argv[++i] : argv[i] + 2;
      struct c2mir_macro_command macro_command = {FALSE, NULL, NULL};

      if (argv[i][1] == 'U') {
        macro_command.name = def;
      } else {
        macro_command.def_p = TRUE;
        macro_command.name = str = reg_malloc (strlen (def) + 1);
        strcpy (str, def);
        if ((bound = strchr (def, '=')) == NULL) {
          macro_command.def = "1";
        } else {
          str[bound - def] = '\0';
          macro_command.def = &macro_command.name[bound - def + 1];
        }
      }
      VARR_PUSH (macro_command_t, macro_commands, macro_command);
    } else if (strcmp (argv[i], "-i") == 0) {
      VARR_PUSH (char_ptr_t, source_file_names, STDIN_SOURCE_NAME);
    } else if (strcmp (argv[i], "-ei") == 0 || strcmp (argv[i], "-eg") == 0
               || strcmp (argv[i], "-el") == 0) {
      VARR_TRUNC (char_ptr_t, exec_argv, 0);
      if (strcmp (argv[i], "-ei") == 0)
        interp_exec_p = TRUE;
      else if (strcmp (argv[i], "-eg") == 0)
        gen_exec_p = TRUE;
      else
        lazy_gen_exec_p = TRUE;
      VARR_PUSH (char_ptr_t, exec_argv, "c2m");
      for (i++; i < argc; i++) VARR_PUSH (char_ptr_t, exec_argv, argv[i]);
    } else if (strcmp (argv[i], "-s") == 0 && i + 1 < argc) {
      code = (uint8_t *) argv[++i];
      code_len = strlen ((char *) code);
    } else if (*argv[i] != '-') {
      VARR_PUSH (char_ptr_t, source_file_names, argv[i]);
    } else if (strcmp (argv[i], "-h") == 0) {
      fprintf (stderr,
               "Usage: %s options (-i | -s \"program\" | source files); where options are:\n",
               argv[0]);
      fprintf (stderr, "\n");
      fprintf (stderr,
               "  -v, -d, -dg -- output work, general debug, or MIR-generator debug info\n");
      fprintf (stderr, "  -E -- output C preprocessed code into stdout\n");
      fprintf (stderr, "  -Dname[=value], -Uname -- predefine or unpredefine macros\n");
      fprintf (stderr, "  -Idir, -Ldir -- add directories to search include headers or lbraries\n");
      fprintf (stderr, "  -fpreprocessed -- assume preprocessed input C\n");
      fprintf (stderr, "  -fsyntax-only -- check C code correctness only\n");
      fprintf (stderr, "  -fpedantic -- assume strict standard input C code\n");
      fprintf (stderr, "  -S, -c -- generate corresponding textual or binary MIR files\n");
      fprintf (stderr, "  -o file -- put output code into given file\n");
      fprintf (stderr, "  -On -- use given optimization level in MIR-generator\n");
      fprintf (stderr,
               "  (-ei | -eg | -el) options -- execute code in the interpreter or (lazily) "
               "generated code with given options\n");
      exit (0);
    } else {
      fprintf (stderr, "unknown command line option %s (use -h for usage) -- goodbye\n", argv[i]);
      exit (1);
    }
  }
  options.include_dirs_num = VARR_LENGTH (char_ptr_t, headers);
  options.include_dirs = VARR_ADDR (char_ptr_t, headers);
  options.macro_commands_num = VARR_LENGTH (macro_command_t, macro_commands);
  options.macro_commands = VARR_ADDR (macro_command_t, macro_commands);
}

static int t_getc (void *data) { return curr_char >= code_len ? EOF : code[curr_char++]; }

static void fancy_abort (void) {
  fprintf (stderr, "Test failed\n");
  abort ();
}

static void *import_resolver (const char *name) {
  void *handler, *sym = NULL;

  for (int i = 0; i < sizeof (std_libs) / sizeof (struct lib); i++)
    if ((handler = std_libs[i].handler) != NULL && (sym = dlsym (handler, name)) != NULL) break;
  if (sym == NULL)
    for (int i = 0; i < VARR_LENGTH (lib_t, cmdline_libs); i++)
      if ((handler = VARR_GET (lib_t, cmdline_libs, i).handler) != NULL
          && (sym = dlsym (handler, name)) != NULL)
        break;
  if (sym == NULL) {
#ifdef _WIN32
    if (strcmp (name, "LoadLibrary") == 0) return LoadLibrary;
    if (strcmp (name, "FreeLibrary") == 0) return FreeLibrary;
    if (strcmp (name, "GetProcAddress") == 0) return GetProcAddress;
#else
    if (strcmp (name, "dlopen") == 0) return dlopen;
    if (strcmp (name, "dlclose") == 0) return dlclose;
    if (strcmp (name, "dlsym") == 0) return dlsym;
    if (strcmp (name, "stat") == 0) return stat;
#endif
    fprintf (stderr, "can not load symbol %s\n", name);
    close_std_libs ();
    exit (1);
  }
  return sym;
}

static int read_func (MIR_context_t ctx) { return t_getc (NULL); }

static const char *get_base_name (const char *name, const char *suffix) {
  const char *res = strrchr (name, slash);

  if (res != NULL) name = res + 1;
  VARR_TRUNC (char, temp_string, 0);
  VARR_PUSH_ARR (char, temp_string, name,
                 (res = strrchr (name, '.')) == NULL ? strlen (name) : res - name);
  VARR_PUSH_ARR (char, temp_string, suffix, strlen (suffix) + 1); /* including zero byte */
  return VARR_ADDR (char, temp_string);
}

static FILE *get_output_file (const char **base_name, const char *source_name, const char *suffix) {
  FILE *f;

  *base_name = get_base_name (source_name, suffix);
  if ((f = fopen (*base_name, "wb")) != NULL) return f;
  fprintf (stderr, "cannot create file %s\n", *base_name);
  exit (1);  // ???
}

int main (int argc, char *argv[], char *env[]) {
  int i, ret_code;
  size_t len;
  const char *source_name;
  MIR_context_t ctx;

  interp_exec_p = gen_exec_p = lazy_gen_exec_p = FALSE;
  VARR_CREATE (void_ptr_t, allocated, 100);
  VARR_CREATE (uint8_t, input, 100);
  VARR_CREATE (char_ptr_t, source_file_names, 32);
  VARR_CREATE (char_ptr_t, exec_argv, 32);
  VARR_CREATE (lib_t, cmdline_libs, 16);
  VARR_CREATE (char_ptr_t, lib_dirs, 16);
  for (i = 0; i < sizeof (std_lib_dirs) / sizeof (char_ptr_t); i++)
    VARR_PUSH (char_ptr_t, lib_dirs, std_lib_dirs[i]);
  ctx = MIR_init ();
  c2mir_init (ctx);
  options.prepro_output_file = NULL;
  init_options (argc, argv);
  for (i = options.module_num = ret_code = 0;; i++, options.module_num++) {
    code = NULL;
    source_name = NULL;
    curr_char = 0;
    VARR_TRUNC (uint8_t, input, 0);
    if (i == 0) {
      if (code == NULL && VARR_LENGTH (char_ptr_t, source_file_names) == 0) {
        fprintf (stderr, "No source file is given -- good bye.\n");
        exit (1);
      }
      if (code != NULL && VARR_LENGTH (char_ptr_t, source_file_names) > 0) {
        fprintf (stderr, "-s and other sources on the command line -- good bye.\n");
        exit (1);
      }
      for (size_t j = 0; j < VARR_LENGTH (char_ptr_t, source_file_names); j++)
        if (strcmp (VARR_GET (char_ptr_t, source_file_names, j), STDIN_SOURCE_NAME) == 0
            && VARR_LENGTH (char_ptr_t, source_file_names) > 1) {
          fprintf (stderr, "-i and sources on the command line -- good bye.\n");
          exit (1);
        }
      if (options.output_file_name == NULL && options.prepro_only_p) {
        options.prepro_output_file = stdout;
      } else if (options.output_file_name != NULL) {
#if defined(__unix__) || defined(__APPLE__)
        if (VARR_LENGTH (char_ptr_t, source_file_names) == 1) {
          source_name = VARR_GET (char_ptr_t, source_file_names, 0);
          if (strcmp (source_name, STDIN_SOURCE_NAME) != 0) {
            struct stat stat1, stat2;

            stat (source_name, &stat1);
            stat (options.output_file_name, &stat2);
            if (stat1.st_dev == stat2.st_dev && stat1.st_ino == stat2.st_ino) {
              fprintf (stderr, "-o %s will rewrite input source file %s -- good bye.\n",
                       options.output_file_name, source_name);
              exit (1);
            }
          }
        }
#endif
        if (options.prepro_only_p) {
          if (options.output_file_name != NULL
              && (options.prepro_output_file = fopen (options.output_file_name, "wb")) == NULL) {
            fprintf (stderr, "cannot create file %s -- good bye.\n", options.output_file_name);
            exit (1);
          }
        } else if ((options.asm_p || options.object_p)
                   && VARR_LENGTH (char_ptr_t, source_file_names) > 1) {
          fprintf (stderr, "-S or -c with -o for multiple files -- good bye.\n");
          exit (1);
        }
      }
    }
    if (code != NULL) { /* command line script: */
      if (i > 0) break;
      source_name = COMMAND_LINE_SOURCE_NAME;
    } else if (code == NULL) { /* stdin input or files give on the command line: */
      int c;
      FILE *f;

      if (i >= VARR_LENGTH (char_ptr_t, source_file_names)) break;
      source_name = VARR_GET (char_ptr_t, source_file_names, i);
      if (strcmp (source_name, STDIN_SOURCE_NAME) == 0) {
        f = stdin;
      } else if ((f = fopen (source_name, "r")) == NULL) {
        fprintf (stderr, "can not open %s -- goodbye\n", source_name);
        exit (1);
      }
      while ((c = getc (f)) != EOF) VARR_PUSH (uint8_t, input, c);
      code_len = VARR_LENGTH (uint8_t, input);
      VARR_PUSH (uint8_t, input, 0);
      code = VARR_ADDR (uint8_t, input);
      fclose (f);
    }
    assert (source_name != NULL);
    len = strlen (source_name);
    if (len >= 5 && strcmp (source_name + len - 5, ".bmir") == 0) {
      MIR_read_with_func (ctx, read_func);
    } else if (len >= 4 && strcmp (source_name + len - 4, ".mir") == 0) {
      DLIST (MIR_module_t) *mlist = MIR_get_module_list (ctx);
      MIR_module_t m, last_m = DLIST_TAIL (MIR_module_t, *mlist);
      const char *base_name;
      FILE *f;

      code_len++; /* include zero byte */
      MIR_scan_string (ctx, (char *) code);
      if (!options.asm_p && !options.prepro_only_p && !options.syntax_only_p && options.object_p) {
        f = get_output_file (&base_name, source_name, ".bmir");
        for (m = last_m == NULL ? DLIST_HEAD (MIR_module_t, *mlist)
                                : DLIST_NEXT (MIR_module_t, last_m);
             m != NULL; m = DLIST_NEXT (MIR_module_t, m))
          MIR_write_module (ctx, f, m);
        if (ferror (f) || fclose (f)) {
          fprintf (stderr, "error in writing file %s\n", base_name);
          ret_code = 1;
        }
      }
    } else {
      const char *base_name;
      FILE *f = (!options.asm_p && !options.object_p
                   ? NULL
                   : get_output_file (&base_name, source_name, options.asm_p ? ".mir" : ".bmir"));

      if (!c2mir_compile (ctx, &options, t_getc, NULL, source_name, f)) ret_code = 1;
    }
  }
  if (options.prepro_output_file != NULL
      && (ferror (options.prepro_output_file)
          || (options.prepro_output_file != stdout && fclose (options.prepro_output_file)))) {
    fprintf (stderr, "error in writing to file %s\n", options.output_file_name);
    ret_code = 1;
  }
  if (ret_code == 0 && !options.prepro_only_p && !options.syntax_only_p && !options.asm_p
      && !options.object_p) {
    MIR_val_t val;
    MIR_module_t module;
    MIR_item_t func, main_func = NULL;
    uint64_t (*fun_addr) (int, void *argv, char *env[]);
    double start_time;

    for (module = DLIST_HEAD (MIR_module_t, *MIR_get_module_list (ctx)); module != NULL;
         module = DLIST_NEXT (MIR_module_t, module)) {
      for (func = DLIST_HEAD (MIR_item_t, module->items); func != NULL;
           func = DLIST_NEXT (MIR_item_t, func))
        if (func->item_type == MIR_func_item && strcmp (func->u.func->name, "main") == 0)
          main_func = func;
      MIR_load_module (ctx, module);
    }
    if (main_func == NULL) {
      fprintf (stderr, "cannot link program w/o main function\n");
      ret_code = 1;
    } else if (!interp_exec_p && !gen_exec_p && !lazy_gen_exec_p) {
      const char *file_name
        = options.output_file_name == NULL ? "a.bmir" : options.output_file_name;
      FILE *f = fopen (file_name, "wb");

      if (f == NULL) {
        fprintf (stderr, "cannot open file %s\n", file_name);
        ret_code = 1;
      } else {
        start_time = real_usec_time ();
        MIR_write (ctx, f);
        if (ferror (f) || fclose (f)) {
          fprintf (stderr, "error in writing file %s\n", file_name);
          ret_code = 1;
        } else if (options.verbose_p) {
          fprintf (stderr, "binary output      -- %.0f msec\n",
                   (real_usec_time () - start_time) / 1000.0);
        }
      }
    } else {
      open_std_libs ();
      MIR_load_external (ctx, "abort", fancy_abort);
      MIR_load_external (ctx, "_MIR_flush_code_cache", _MIR_flush_code_cache);
      if (interp_exec_p) {
        MIR_link (ctx, MIR_set_interp_interface, import_resolver);
        start_time = real_usec_time ();
        MIR_interp (ctx, main_func, &val, 3, (MIR_val_t){.i = VARR_LENGTH (char_ptr_t, exec_argv)},
                    (MIR_val_t){.a = (void *) VARR_ADDR (char_ptr_t, exec_argv)},
                    (MIR_val_t){.a = (void *) env});
        ret_code = val.i;
        if (options.verbose_p) {
          fprintf (stderr, "  execution       -- %.0f msec\n",
                   (real_usec_time () - start_time) / 1000.0);
          fprintf (stderr, "exit code: %lu\n", (long unsigned) ret_code);
        }
      } else {
        MIR_gen_init (ctx);
        if (optimize_level >= 0) MIR_gen_set_optimize_level (ctx, (unsigned) optimize_level);
        if (gen_debug_p) MIR_gen_set_debug_file (ctx, stderr);
        MIR_link (ctx, gen_exec_p ? MIR_set_gen_interface : MIR_set_lazy_gen_interface,
                  import_resolver);
        fun_addr = MIR_gen (ctx, main_func);
        start_time = real_usec_time ();
        ret_code
          = fun_addr (VARR_LENGTH (char_ptr_t, exec_argv), VARR_ADDR (char_ptr_t, exec_argv), env);
        if (options.verbose_p) {
          fprintf (stderr, "  execution       -- %.0f msec\n",
                   (real_usec_time () - start_time) / 1000.0);
          fprintf (stderr, "exit code: %d\n", ret_code);
        }
        MIR_gen_finish (ctx);
      }
    }
  }
  close_cmdline_libs ();
  close_std_libs ();
  c2mir_finish (ctx);
  MIR_finish (ctx);
  VARR_DESTROY (char, temp_string);
  VARR_DESTROY (char_ptr_t, headers);
  VARR_DESTROY (macro_command_t, macro_commands);
  VARR_DESTROY (char_ptr_t, lib_dirs);
  VARR_DESTROY (lib_t, cmdline_libs);
  VARR_DESTROY (char_ptr_t, source_file_names);
  VARR_DESTROY (char_ptr_t, exec_argv);
  VARR_DESTROY (uint8_t, input);
  for (size_t i = 0; i < VARR_LENGTH (void_ptr_t, allocated); i++)
    free (VARR_GET (void_ptr_t, allocated, i));
  VARR_DESTROY (void_ptr_t, allocated);
  return ret_code;
}
