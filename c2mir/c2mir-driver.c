#include <string.h>
#include <stdlib.h>
#include <dlfcn.h>
#include <sys/time.h>
#if defined(__unix__) || defined(__APPLE__)
#include <sys/stat.h>
#endif

#include "c2mir.h"
#include "mir-gen.h"

static double real_usec_time (void) {
  struct timeval tv;

  gettimeofday (&tv, NULL);
  return tv.tv_usec + tv.tv_sec * 1000000.0;
}

static struct c2mir_options options;

static size_t curr_char, code_len;
static const uint8_t *code;

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

static void init_options (int argc, char *argv[]) {
  const char *str;
  int c;

  options.message_file = stderr;
  options.debug_p = options.verbose_p = options.asm_p = options.object_p = FALSE;
  options.output_file_name = NULL;
  options.no_prepro_p = options.prepro_only_p = options.syntax_only_p = options.pedantic_p = FALSE;
  VARR_CREATE (char, temp_string, 0);
  VARR_CREATE (char_ptr_t, headers, 0);
  VARR_CREATE (macro_command_t, macro_commands, 0);
  for (int i = 1; i < argc; i++) {
    if (strcmp (argv[i], "-d") == 0) {
      options.verbose_p = options.debug_p = TRUE;
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
    } else if (strcmp (argv[i], "-o") == 0) {
      if (i + 1 >= argc)
        fprintf (stderr, "-o without argument\n");
      else
        options.output_file_name = argv[++i];
    } else if (strncmp (argv[i], "-I", 2) == 0) {
      char *i_dir;
      const char *dir = strlen (argv[i]) == 2 && i + 1 < argc ? argv[++i] : argv[i] + 2;

      if (*dir == '\0') continue;
      i_dir = malloc (strlen (dir) + 1);
      strcpy (i_dir, dir);
      VARR_PUSH (char_ptr_t, headers, i_dir);
    } else if (strncmp (argv[i], "-U", 2) == 0 || strncmp (argv[i], "-D", 2) == 0) {
      char *str;
      const char *bound, *def = strlen (argv[i]) == 2 && i + 1 < argc ? argv[++i] : argv[i] + 2;
      struct c2mir_macro_command macro_command = {FALSE, NULL, NULL};

      if (argv[i][1] == 'U') {
        macro_command.name = def;
      } else {
        macro_command.def_p = TRUE;
        macro_command.name = str = malloc (strlen (def) + 1);
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
    } else {
      fprintf (stderr, "unknown command line option %s (use -h for usage) -- goodbye", argv[i]);
      exit (1);
    }
  }
  options.include_dirs_num = VARR_LENGTH (char_ptr_t, headers);
  options.include_dirs = VARR_ADDR (char_ptr_t, headers);
  options.macro_commands_num = VARR_LENGTH (macro_command_t, macro_commands);
  options.macro_commands = VARR_ADDR (macro_command_t, macro_commands);
}

static int t_getc (void) { return curr_char >= code_len ? EOF : code[curr_char++]; }

static void t_ungetc (int c) {
  if (c == EOF) {
    assert (curr_char >= code_len);
  } else {
    assert (curr_char != 0 && code[curr_char - 1] == c);
    curr_char--;
  }
}

static void fancy_abort (void) {
  fprintf (stderr, "Test failed\n");
  abort ();
}

static int fancy_printf (const char *fmt, ...) { abort (); }

static struct lib {
  char *name;
  void *handler;
} std_libs[] = { {"/lib64/libc.so.6", NULL}, {"/lib64/libm.so.6", NULL} };

static void close_libs (void) {
  for (int i = 0; i < sizeof (std_libs) / sizeof (struct lib); i++)
    if (std_libs[i].handler != NULL) dlclose (std_libs[i].handler);
}

static void open_libs (void) {
  for (int i = 0; i < sizeof (std_libs) / sizeof (struct lib); i++)
    std_libs[i].handler = dlopen (std_libs[i].name, RTLD_LAZY);
}

static void *import_resolver (const char *name) {
  void *sym = NULL;

  for (int i = 0; i < sizeof (std_libs) / sizeof (struct lib); i++)
    if (std_libs[i].handler != NULL && (sym = dlsym (std_libs[i].handler, name)) != NULL) break;
  if (sym == NULL) {
    if (strcmp (name, "dlopen") == 0) return dlopen;
    if (strcmp (name, "dlclose") == 0) return dlclose;
    if (strcmp (name, "dlsym") == 0) return dlsym;
    if (strcmp (name, "stat") == 0) return stat;
    fprintf (stderr, "can not load symbol %s\n", name);
    close_libs ();
    exit (1);
  }
  return sym;
}

static int read_func (MIR_context_t ctx) { return t_getc (); }

static const char *get_base_name (const char *name, const char *suffix) {
#ifdef _WIN32
  const char *res = strrchr (name, '\\');
#else
  const char *res = strrchr (name, '/');
#endif
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
  VARR_CREATE (uint8_t, input, 100);
  VARR_CREATE (char_ptr_t, source_file_names, 32);
  VARR_CREATE (char_ptr_t, exec_argv, 32);
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
        fprintf (stderr, "can not open %s -- goodbye", source_name);
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

      if (!c2mir_compile (ctx, &options, t_getc, t_ungetc, source_name, f)) ret_code = 1;
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
      open_libs ();
      MIR_load_external (ctx, "abort", fancy_abort);
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
          fprintf (stderr, "exit code: %lu\n", ret_code);
        }
      } else {
        MIR_gen_init (ctx);
#if MIR_GEN_DEBUG
        MIR_gen_set_debug_file (ctx, stderr);
#endif
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
  close_libs ();
  c2mir_finish (ctx);
  MIR_finish (ctx);
  VARR_DESTROY (char, temp_string);
  VARR_DESTROY (char_ptr_t, headers);
  VARR_DESTROY (macro_command_t, macro_commands);
  VARR_DESTROY (char_ptr_t, source_file_names);
  VARR_DESTROY (char_ptr_t, exec_argv);
  VARR_DESTROY (uint8_t, input);
  return ret_code;
}
