const std = @import("std");
const parse = @import("parse.zig");
const dpll = @import("dpll.zig");

pub const Clause = struct {
    allocator: std.mem.Allocator,
    /// if a literal exists in this map it is part of the clause
    /// note: x and !x are treated as distinct literals for the purposes of this map
    literals: std.AutoHashMap(i32, void),

    pub fn init(allocator: std.mem.Allocator) Clause {
        return Clause{
            .allocator = allocator,
            .literals = std.AutoHashMap(i32, void).init(allocator),
        };
    }

    pub fn initWithLiterals(allocator: std.mem.Allocator, literals: []const i32) Clause {
        var clause = Clause.init(allocator);
        for (literals) |lit| {
            try clause.add(lit);
        }
        return clause;
    }

    pub fn deinit(self: *Clause) void {
        self.literals.deinit();
    }

    pub fn add(self: *Clause, literal: i32) !void {
        try self.literals.put(literal, {});
    }

    pub fn remove(self: *Clause, literal: i32) void {
        _ = self.literals.remove(literal);
    }

    pub fn contains(self: *Clause, literal: i32) bool {
        return self.literals.contains(literal);
    }

    pub fn isEmpty(self: *Clause) bool {
        return self.literals.count() == 0;
    }

    pub fn format(self: *Clause, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        var it = self.literals.iterator();
        try writer.print("clause@{p} {", .{self});
        while (it.next()) |entry| {
            try writer.print(" {} ", .{entry.key_ptr.*});
        }
        try writer.print("}", .{});
    }
};

pub const Formula = struct {
    allocator: std.mem.Allocator,
    clauses: std.ArrayList(Clause),

    pub fn init(allocator: std.mem.Allocator) Formula {
        return Formula{
            .allocator = allocator,
            .clauses = std.ArrayList(Clause).init(allocator),
        };
    }

    pub fn deinit(self: *Formula) void {
        for (self.clauses.items) |*clause| {
            clause.deinit();
        }
        self.clauses.deinit();
    }

    pub fn append(self: *Formula, literals: []const i32) !void {
        try self.clauses.append(Clause.initWithLiterals(self.allocator, literals));
    }

    pub fn pop(self: *Formula) void {
        self.clauses.items[self.clauses.items.len - 1].deinit();
        _ = self.clauses.pop();
    }

    pub fn format(self: *Formula, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.print("formula@{p} {\n", .{self});
        for (self.clauses.items, 0..) |clause, i| {
            try writer.print("\t({d}) {any}\n", .{ i, clause });
        }
        try writer.print("}", .{});
    }
};

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

    var clauses = try parse.parseDimacs(allocator, dimacs_file_path);

    // todo: this is stupid, parseDimacs should return this somehow
    var num_variables: usize = 0;
    for (clauses.items) |clause| {
        for (clause.items) |lit| {
            num_variables = @max(num_variables, @abs(lit));
        }
    }

    var assignment = std.ArrayList(i32).init(allocator);
    defer assignment.deinit();

    const result = dpll.recursiveSolve(allocator, &clauses, &assignment);
    std.debug.print("Result: {} {any}\n", .{ result, assignment.items });
}
