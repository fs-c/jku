### `canco`

Determine [**can**onical **co**vers](https://en.wikipedia.org/wiki/Canonical_cover) (and [attribute closures](https://en.wikipedia.org/wiki/Functional_dependency#Closure_of_a_set_of_attributes)) from a set of [functional dependencies](https://en.wikipedia.org/wiki/Functional_dependency).

```bash
$ npm i -g canco
$ canco -h
Usage:
    canco --help/-h
        Outputs this help message
    canco [functional dependencies]
        Outputs the canonical cover for the given set of functional dependencies 
        (A-B,B-CD,D-A)
    canco closure [attributes] [functional dependencies]
        Outputs the closure of the given set of attributes (A,B,C,...) for the 
        given set of functional dependencies (A-B,B-CD,D-A).

Set notation:
    Sets are comma (but not space!) delimited strings: A,B,C is recognized but 
    A, B, C is not
```

`canco` can also be consumed as a regular package.

```js
const { canonicalCover, attributeClosure, utils } = require('canco');

const deps = utils.stringToDeps('A-B,B-A');

const cover = canonicalCover({ ...deps });
const attrs = attributeClosure('AB', {...deps });
```

At the moment the codebase is small enought that I'd recommend simply reading through the code to get an overview of the exposed API and its functionality.
