const std = @import("std");

// todo: debatable if this should be generic or not
pub fn Clause(comptime LiteralType: type) type {
    return struct {
        const Self = @This();

        allocator: std.mem.Allocator,
        /// if a literal exists in this map it is part of the clause
        /// note: x and !x are treated as distinct literals
        literals: std.AutoHashMap(LiteralType, void),

        pub fn init(allocator: std.mem.Allocator) Self {
            return .{
                .allocator = allocator,
                .literals = std.AutoHashMap(LiteralType, void).init(allocator),
            };
        }

        pub fn initFromLiterals(allocator: std.mem.Allocator, literals: []const LiteralType) Self {
            var clause = Self.init(allocator);
            for (literals) |lit| {
                clause.add(lit);
            }
            return clause;
        }

        pub fn deinit(self: *Self) void {
            self.literals.deinit();
        }

        pub fn add(self: *Self, literal: LiteralType) void {
            self.literals.put(literal, {}) catch unreachable;
        }

        pub fn remove(self: *Self, literal: LiteralType) bool {
            return self.literals.remove(literal);
        }

        pub fn contains(self: *const Self, literal: LiteralType) bool {
            return self.literals.contains(literal);
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.literals.count() == 0;
        }

        pub fn eq(self: *const Self, other: Self) bool {
            if (self.literals.count() != other.literals.count()) {
                return false;
            }

            var it = self.literals.keyIterator();
            while (it.next()) |lit| {
                if (!other.contains(lit.*)) {
                    return false;
                }
            }

            return true;
        }

        pub fn eqToSlice(self: *const Self, other: []const LiteralType) bool {
            if (self.literals.count() != other.len) {
                return false;
            }

            for (other) |lit| {
                if (!self.contains(lit)) {
                    return false;
                }
            }

            return true;
        }

        pub fn format(self: *const Self, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            var it = self.literals.keyIterator();
            try writer.print("{p} (", .{&self});
            while (it.next()) |lit| {
                try writer.print(" {d}", .{lit.*});
            }
            try writer.print(" )", .{});
        }
    };
}

test Clause {
    var clause = Clause(i32).init(std.testing.allocator);
    defer clause.deinit();

    clause.add(1);
    clause.add(-2);

    try std.testing.expect(clause.eq(clause));

    var equal_clause = Clause(i32).initFromLiterals(std.testing.allocator, &[_]i32{ -2, 1 });
    defer equal_clause.deinit();
    try std.testing.expect(clause.eq(equal_clause));
    try std.testing.expect(clause.eqToSlice(&[_]i32{ -2, 1 }));

    var unequal_clause = Clause(i32).initFromLiterals(std.testing.allocator, &[_]i32{ 1, 2 });
    defer unequal_clause.deinit();
    try std.testing.expect(!clause.eq(unequal_clause));
    try std.testing.expect(!clause.eqToSlice(&[_]i32{ 1, 2 }));

    try std.testing.expect(clause.contains(1));
    try std.testing.expect(clause.contains(-2));

    try std.testing.expect(clause.remove(1));

    try std.testing.expect(!clause.contains(1));
    try std.testing.expect(clause.contains(-2));

    try std.testing.expect(!clause.isEmpty());

    try std.testing.expect(clause.remove(-2));

    try std.testing.expect(clause.isEmpty());

    var another_clause = Clause(i32).initFromLiterals(std.testing.allocator, &[_]i32{ -1, 2, -2, 3, 4, 5 });
    defer another_clause.deinit();

    try std.testing.expect(another_clause.eqToSlice(&[_]i32{ -1, 2, -2, 3, 4, 5 }));

    try std.testing.expect(!another_clause.remove(1));
    try std.testing.expect(another_clause.remove(-2));

    try std.testing.expect(another_clause.eqToSlice(&[_]i32{ -1, 2, 3, 4, 5 }));
}

pub const Formula = struct {
    const Self = @This();
    // todo: if clause is generic, then this probably should be too
    pub const LiteralType = i16;

    allocator: std.mem.Allocator,
    clauses: std.ArrayList(Clause(LiteralType)),

    pub fn init(allocator: std.mem.Allocator) Self {
        return .{
            .allocator = allocator,
            .clauses = std.ArrayList(Clause(LiteralType)).init(allocator),
        };
    }

    pub fn initFromClauseSlices(allocator: std.mem.Allocator, clauses: []const []const LiteralType) Self {
        var formula = Self.init(allocator);
        for (clauses) |clause| {
            formula.append(Clause(LiteralType).initFromLiterals(allocator, clause)) catch unreachable;
        }
        return formula;
    }

    pub fn deinit(self: *Self) void {
        for (self.clauses.items) |*clause| {
            clause.deinit();
        }
        self.clauses.deinit();
    }

    pub fn append(self: *Self, clause: Clause(LiteralType)) !void {
        try self.clauses.append(clause);
    }

    pub fn swapRemove(self: *Self, index: usize) void {
        self.clauses.items[index].deinit();
        _ = self.clauses.swapRemove(index);
    }

    pub fn isEmpty(self: *Self) bool {
        return self.clauses.items.len == 0;
    }

    /// note: this has quadratic complexity, only use for testing
    pub fn eqToSlice(self: *Self, other: []const []const LiteralType) bool {
        if (self.clauses.items.len != other.len) {
            return false;
        }

        for (self.clauses.items) |clause| {
            var found = false;
            for (other) |other_clause| {
                if (clause.eqToSlice(other_clause)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }

        return true;
    }

    pub fn format(self: *const Self, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.print("{p} (\n", .{&self});
        for (self.clauses.items, 0..) |clause, i| {
            try writer.print("\t[{d}] {any} {d}\n", .{ i, clause, clause.literals.count() });
        }
        try writer.print(")", .{});
    }
};

test Formula {
    var formula = Formula.init(std.testing.allocator);
    defer formula.deinit();

    var clause = Clause(Formula.LiteralType).initFromLiterals(std.testing.allocator, &[_]Formula.LiteralType{ 1, -2 });
    errdefer clause.deinit();

    try formula.append(clause);

    try std.testing.expect(formula.clauses.items.len == 1);
    try std.testing.expect(formula.clauses.items[0].eq(clause));

    formula.swapRemove(0);

    try std.testing.expect(formula.clauses.items.len == 0);

    var another_formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 1, -2 },
        &[_]Formula.LiteralType{ -1, -2, 3 },
    });
    defer another_formula.deinit();

    try std.testing.expect(another_formula.clauses.items.len == 2);

    try std.testing.expect(another_formula.eqToSlice(&[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ -1, 3, -2 },
        &[_]Formula.LiteralType{ 1, -2 },
    }));

    try std.testing.expect(!another_formula.eqToSlice(&[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 1, -2 },
        &[_]Formula.LiteralType{ -1, -2 },
    }));

    try std.testing.expect(!another_formula.isEmpty());

    var empty_formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{});
    defer empty_formula.deinit();

    try std.testing.expect(empty_formula.isEmpty());
}
