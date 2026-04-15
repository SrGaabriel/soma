const std = @import("std");

pub fn build(b: *std.Build) void {
    const default_target: std.Target.Query = if (@import("builtin").os.tag == .windows)
        .{ .os_tag = .windows, .abi = .gnu }
    else
        .{};
    const target = b.standardTargetOptions(.{ .default_target = default_target });
    const optimize: std.builtin.OptimizeMode = b.option(
        std.builtin.OptimizeMode,
        "optimize",
        "Optimization mode (default: ReleaseFast)",
    ) orelse .ReleaseFast;

    const pool_stats = b.option(
        bool,
        "pool-stats",
        "Enable atomic pool-allocator counters (exported as soma_pool_stats).",
    ) orelse false;
    const no_main = b.option(
        bool,
        "no-main",
        "Omit the `main` wrapper so the runtime can be linked into a foreign host program.",
    ) orelse false;

    const options = b.addOptions();
    options.addOption(bool, "pool_stats", pool_stats);
    options.addOption(bool, "no_main", no_main);

    const root_module = b.createModule(.{
        .root_source_file = b.path("soma_runtime.zig"),
        .target = target,
        .optimize = optimize,
        .pic = true,
        .strip = optimize != .Debug,
    });
    root_module.addOptions("soma_runtime_options", options);
    root_module.link_libc = true;

    const lib = b.addLibrary(.{
        .name = "soma_runtime",
        .root_module = root_module,
        .linkage = .static,
    });

    b.installArtifact(lib);
    const install_archive = b.addInstallFileWithDir(
        lib.getEmittedBin(),
        .prefix,
        "libsoma_runtime.a",
    );
    b.getInstallStep().dependOn(&install_archive.step);

    const test_options = b.addOptions();
    test_options.addOption(bool, "pool_stats", pool_stats);
    test_options.addOption(bool, "no_main", true);

    const test_mod = b.createModule(.{
        .root_source_file = b.path("soma_runtime.zig"),
        .target = target,
        .optimize = optimize,
    });
    test_mod.addOptions("soma_runtime_options", test_options);
    test_mod.link_libc = true;

    const tests = b.addTest(.{ .root_module = test_mod });
    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run runtime unit tests");
    test_step.dependOn(&run_tests.step);
}
