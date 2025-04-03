const std = @import("std");
const parse = @import("parse.zig");
const dpll = @import("dpll.zig");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const allocator = arena.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    const dimacs_file_path = if (args.len == 2) args[1] else {
        std.debug.print("Usage: {s} <dimacs_file>\n", .{args[0]});
        return;
    };

    var formula = try parse.parseDimacs(allocator, dimacs_file_path);

    var assignment = std.ArrayList(i32).init(allocator);
    defer assignment.deinit();

    const result = dpll.recursiveSolve(allocator, &formula, &assignment);
    std.debug.print("Result: {} {any}\n", .{ result, assignment.items });
}
