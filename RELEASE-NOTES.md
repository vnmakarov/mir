# Major changes from v0.1.1 to v0.1.2:

 * Numerous bugs were fixed
 * Shared library is now built and installed beside the static library
 * MIR was ported to musl-based Linux systems, e.g. alpine Linux
 * Generator was improved
   * Register allocator was significantly sped up
   * Alloca code generation was improved (alloca insn consolidation)
 * No red zone x86_64 ABI is now supported
 * Generator debug info were enhanced and improved
 * Documentation in Chinese was added
