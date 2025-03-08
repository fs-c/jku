#!/usr/bin/env python3
# Example by Max Heisinger, https://maxheisinger.at | Symbolic AI @ JKU, 2025
# License: CC0 / Public Domain
#
# Building CaDiCaL:
# ./configure CXXFLAGS=-fPIC && cd build && make -j8 libcadical.a && g++ -fpic -g -std=c++17 -O3 -I../src/ -shared -o libcadical.so ../src/ccadical.cpp libcadical.a
#
# Source: https://github.com/arminbiere/cadical

import argparse
import ctypes
from ctypes import cdll

cadical = cdll.LoadLibrary('./libcadical.so')

# CaDiCaL binding
class CaDiCaL:
    def __init__(self, verbose=False):
        self.ccadical_init = cadical.ccadical_init
        self.ccadical_init.restype = ctypes.c_void_p

        self.ccadical_add = cadical.ccadical_add
        self.ccadical_add.argtypes = [ ctypes.c_void_p, ctypes.c_int ]

        self.ccadical_solve = cadical.ccadical_solve
        self.ccadical_solve.restype = ctypes.c_int
        self.ccadical_solve.argtypes = [ ctypes.c_void_p ]

        self.ccadical_val = cadical.ccadical_val
        self.ccadical_val.restype = ctypes.c_int
        self.ccadical_val.argtypes = [ ctypes.c_void_p ]

        self.ccadical_release = cadical.ccadical_release
        self.ccadical_release.argtypes = [ ctypes.c_void_p ]

        self.solver = self.ccadical_init()

        self.var_counter = 0
        self.verbose = verbose

    def newvar(self):
        self.var_counter += 1
        return self.var_counter

    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_value, traceback):
        cadical.ccadical_release(self.solver)

    def add(self, lit: int):
        if self.verbose:
            if lit == 0:
                print("0")
            else:
                print(f"{lit} ", end='')
        self.ccadical_add(self.solver, lit)

    def solve(self):
        return cadical.ccadical_solve(self.solver)

    def val(self, lit: int):
        return cadical.ccadical_val(self.solver, lit) > 0

    def unary(self, a: int):
        self.add(a)
        self.add(0)

    def binary(self, a: int, b: int):
        self.add(a)
        self.add(b)
        self.add(0)

    def ternary(self, a: int, b: int, c: int):
        self.add(a)
        self.add(b)
        self.add(c)
        self.add(0)

    def land(self, *lits):
        # t <-> (a & b & c & ...)
        # equivalent to
        # (!t a) & (!t b) & (!t c) & ... & (t !a !b !c ...)
        #
        # Proof:
        # https://maximaximal.github.io/limboole/#0(t%20%3C-%3E%20(a%20%26%20b%20%26%20c))%20%3C-%3E%20((!t%20%7C%20a)%20%26%20(!t%20%7C%20b)%20%26%20(!t%20%7C%20c)%20%26%20(t%20%7C%20!a%20%7C%20!b%20%7C%20!c))
        t = self.newvar()
        for x in lits:
            self.binary(-t, x)

        for x in lits:
            self.add(-x)
        self.add(t)
        self.add(0)

        return t

    def lor(self, *lits):
        # t <-> (a | b | c | ...)
        # equivalent to
        # (!t a b c ...) (t !a) (t !b) (t !c) ...
        #
        # Proof:
        # https://maximaximal.github.io/limboole/#0(t%20%3C-%3E%20(a%20%7C%20b%20%7C%20c))%20%3C-%3E%20((t%20%7C%20!a)%20%26%20(t%20%7C%20!b)%20%26%20(t%20%7C%20!c)%20%26%20(!t%20%7C%20a%20%7C%20b%20%7C%20c))
        t = self.newvar()
        for x in lits:
            self.add(x)
        self.add(-t)
        self.add(0)

        for x in lits:
            self.binary(t, -x)

        return t

    def limpl(self, l, r):
        # t <-> (l -> r)
        # eqivalent to
        # (t l) (t !r) (!t l r)
        #
        # Proof:
        # https://maximaximal.github.io/limboole/#0(t%20%3C-%3E%20(l%20-%3E%20r))%20%3C-%3E%20((t%20%7C%20l)%20%26%20(t%20%7C%20!r)%20%26%20(!t%20%7C%20!l%20%7C%20r))
        t = self.newvar()
        self.binary(t, l)
        self.binary(t, -r)
        self.ternary(-t, l, r)

        return t

    def liff(self, l, r):
        # t <-> (l <-> r)
        # eqivalent to
        # (t !l !r) (t l r) (!t !l r) (!t l !r)
        #
        # Proof:
        # https://maximaximal.github.io/limboole/#0(t%20%3C-%3E%20(l%20%3C-%3E%20r))%20%3C-%3E%20((t%20%7C%20!l%20%7C%20!r)%20%26%20(t%20%7C%20l%20%7C%20r)%20%26%20(!t%20%7C%20!l%20%7C%20r)%20%26%20(!t%20%7C%20l%20%7C%20!r))
        t = self.newvar()
        self.ternary(t, -l, -r)
        self.ternary(t, l, r)
        self.ternary(-t, -l, r)
        self.ternary(-t, l, -r)

        return t

    # Many other logical operators could be defined.

def demorgan(s):
    # Let's encode De Morgan!
    # !(a & b) <-> (!a | !b)
    #     L    <->     R

    a = s.newvar()
    b = s.newvar()

    L = s.land(a, b)
    R = s.lor(-a, -b)

    equi = s.liff(-L, R)

    # Now, let's search for a counter example! Check for !equi.
    s.unary(-equi)

    res = s.solve()

    if res == 20:
        print("Proved De-Morgan! :D")
    else:
        counter_a = s.val(a)
        counter_b = s.val(b)
        print(f"De Morgan is broken by a:{counter_a}, b:{counter_b}")
        print("THE UNIVERSE IS ALL WRONG https://www.youtube.com/watch?v=a9EuLkYBf2s")

def party(s):
    # Propositional Variables
    inviteAlice = s.newvar()
    inviteBob = s.newvar()
    inviteCecile = s.newvar()
    inviteDavid = s.newvar()
    inviteEva = s.newvar()
    inviteFred = s.newvar()

    # Constraints
    inviteMarried = s.land(s.liff(inviteAlice, inviteBob), s.liff(inviteCecile, inviteDavid))
    ifAliceThenCecile = s.limpl(inviteAlice, inviteCecile)
    eitherDavidOrEva = -s.liff(inviteEva, inviteDavid)
    inviteBobAndFred = s.land(inviteBob, inviteFred)

    # Force all constraints.
    s.unary(inviteMarried)
    s.unary(ifAliceThenCecile)
    s.unary(eitherDavidOrEva)
    s.unary(inviteBobAndFred)

    # Solve the problem and get an assignment.
    res = s.solve()
    if res == 20:
        print("Too many constraints for this party!")
    else:
        print(f"Invite Alice: {s.val(inviteAlice)}")
        print(f"Invite Bob: {s.val(inviteBob)}")
        print(f"Invite Cecile: {s.val(inviteCecile)}")
        print(f"Invite David: {s.val(inviteDavid)}")
        print(f"Invite Eva: {s.val(inviteEva)}")
        print(f"Invite Fred: {s.val(inviteFred)}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(prog='Tseitin Demo')
    parser.add_argument('--demorgan', action='store_true')
    parser.add_argument('--party', action='store_true')
    parser.add_argument('--verbose', action='store_true')

    args = parser.parse_args()

    v = args.verbose

    if args.demorgan:
        with CaDiCaL(verbose=v) as s:
            demorgan(s)

    if args.party:
        with CaDiCaL(verbose=v) as s:
            party(s)

    if not args.demorgan and not args.party:
        print("Call with --demorgan or --party")

