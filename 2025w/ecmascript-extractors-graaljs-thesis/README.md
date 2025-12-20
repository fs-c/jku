abstract: 6-8 sentences. what problem is being solved. how is this done. what is the result: what works, how many tests, etc.; whe benefits.

intro: basically extended abstract. why is stage 1 being implemented (= just wanted rough POC). contributions: what did this work do? include code example from ch 3.

background: what is js/ecma (context, where used etc.). proposal process.

extractors: more elaborate example. move prior art to new chapter (related work). make all (most) listings floats.

testing -> evaluation: add interesting edge cases.

conclusion: what did we actually do. basically condensed intro again -> what is now possible. maybe future work.

---

### edge cases/bugs discovered in testing etc.

- the newline thing (see notes & issue), double check if that is still an issue
- there will be an issue with if condition in catch clause (nashorn extension) in combination with extractors (parser line 3895)
- array destructuring with extractors broken (but not without): `const [Pair(x, y), other] = [p, "value"];`, x and y as expected but other == null
  - caused by invoking a read iterator next node more than once as part of the extractor syntax translation
- scoping of variables introduced in a binding extractor statement
  - didn't properly set the variables as declared to mark their scope, defaulted to global scope (strange behavior from graaljs imo)

---

### abby session

- inconsistent emph usage
- inconsistent capitalizations
- run-on sentences
- briefly explain visitor pattern where it is mentioned
- replace instances of "spec" with "specification"
