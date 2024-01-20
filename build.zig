const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib = b.addStaticLibrary(.{
        .name = "mir",
        .target = target,
        .optimize = optimize,
    });
    lib.disable_sanitize_c = true;
    lib.linkLibC();
    lib.addCSourceFiles(&.{
        "mir.c",
        "mir-gen.c",
    }, &.{});

    b.installArtifact(lib);
}
