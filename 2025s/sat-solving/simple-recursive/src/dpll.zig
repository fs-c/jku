const std = @import("std");

fn Clause(comptime N: usize) type {
    return struct {
        const Self = @This();

        literals: [N]i32,


    };
}

std.EnumMap;

pub fn recursiveSolve(allocator: std.mem.Allocator, clauses: *std.ArrayList(std.ArrayList(i32)), assignment: *std.ArrayList(i32)) bool {
    while (getFirstUnitClause(clauses)) |literal| {
        // todo: other solutions also modify assignment here?
        propagateBinaryConstraint(clauses, literal);
    }

    if (clauses.items.len == 0) {
        return true;
    }

    for (clauses.items) |clause| {
        std.debug.print("{any} ", .{clause.items});
        if (clause.items.len == 0) {
            return false;
        }
    }

    // shouldn't be possible to not have a literal here, given the above checks
    const literal = getFirstLiteral(clauses) orelse {
        std.debug.print("{any} {d}\n", .{ clauses.items, clauses.items.len });
        unreachable;
    };

    var positiveClause = std.ArrayList(i32).init(allocator);
    errdefer positiveClause.deinit();
    positiveClause.append(literal) catch unreachable;

    clauses.append(positiveClause) catch unreachable;
    assignment.append(literal) catch unreachable;
    if (recursiveSolve(allocator, clauses, assignment)) {
        return true;
    }

    var negativeClause = std.ArrayList(i32).init(allocator);
    errdefer negativeClause.deinit();
    negativeClause.append(-literal) catch unreachable;

    _ = clauses.pop();
    _ = assignment.pop();

    clauses.append(negativeClause) catch unreachable;
    assignment.append(-literal) catch unreachable;
    if (recursiveSolve(allocator, clauses, assignment)) {
        return true;
    }

    _ = clauses.pop();
    _ = assignment.pop();

    return false;
}

fn getFirstUnitClause(clauses: *std.ArrayList(std.ArrayList(i32))) ?i32 {
    for (clauses.items) |clause| {
        if (clause.items.len == 1) {
            return clause.items[0];
        }
    }
    return null;
}

fn getFirstLiteral(clauses: *std.ArrayList(std.ArrayList(i32))) ?i32 {
    for (clauses.items) |clause| {
        for (clause.items) |lit| {
            return lit;
        }
    }
    return null;
}

/// remove all clauses that contain the literal and remove all occurences of !literal
fn propagateBinaryConstraint(clauses: *std.ArrayList(std.ArrayList(i32)), literal: i32) void {
    // iterate backwards to avoid issues with index shifting, because we remove during iteration
    var i: usize = clauses.items.len;
    while (i > 0) {
        i -= 1;
        var clause = &clauses.items[i];

        std.debug.print("considering clause: {any} ({d})\n", .{ clause.items, literal });

        if (std.mem.indexOfScalar(i32, clause.items, literal) != null) {
            _ = clauses.swapRemove(i);
            std.debug.print("removed clause\n", .{});
        } else if (std.mem.indexOfScalar(i32, clause.items, -literal)) |indexOfNegation| {
            _ = clause.swapRemove(indexOfNegation);
            std.debug.print("removed negation: {any}\n", .{clause.items});
        }
    }
}

test "propagateBinaryConstraint" {
    const allocator = std.testing.allocator;

    var clauses = std.ArrayList(std.ArrayList(i32)).init(allocator);
    defer clauses.deinit();

    var clause1 = std.ArrayList(i32).init(allocator);
    defer clause1.deinit();
    try clause1.appendSlice(&[_]i32{ 1, 2, 3 });
    try clauses.append(clause1);

    var clause2 = std.ArrayList(i32).init(allocator);
    defer clause2.deinit();
    try clause2.appendSlice(&[_]i32{ -1, 2, 3 });
    try clauses.append(clause2);

    var clause3 = std.ArrayList(i32).init(allocator);
    defer clause3.deinit();
    try clause3.appendSlice(&[_]i32{ 4, -5, -6 });
    try clauses.append(clause3);

    propagateBinaryConstraint(&clauses, 1);

    try std.testing.expectEqual(clauses.items.len, 2);
    try std.testing.expectEqualSlices(i32, &[_]i32{ 3, 2 }, clauses.items[1].items);
    try std.testing.expectEqualSlices(i32, &[_]i32{ 4, -5, -6 }, clauses.items[0].items);
}
