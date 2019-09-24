# AutBound: Code generator for abstract syntax trees

## Usage

The executable can be used from the command line with the following arguments:

```
autbound SOURCE_FILE OUTPUT_LANGUAGE VARIABLE_TYPE OUTPUT_NAME
```

For example, if we want to generate a Haskell module called `FCoBase` from the FCo specification, using string-based variables, we would issue the command:

```
autbound "Specifications/FCo.txt" Haskell String FCoBase
```

This will generate the file `FCoBase.hs` in the current directory.

The following options are currently available:
- `OUTPUT_LANGUAGE`: `Haskell`, `OCaml`
- `VARIABLE_TYPE`: `DeBruijn`, `String`

## Language descriptions

Language descriptions are simple text files. They consist of four different parts:

- Import declarations
- Namespace declarations
- Sort declarations
- Native code

None of these sections are mandatory, but their order is fixed.

For examples of language descriptions, see the `Specifications` directory.

### Import declarations

If your native code uses other modules, you can declare the import statements with the following syntax at the top of your language description:

```
import (MODULE_NAME) [ ( ENTITY [ ENTITY]* ) ]
```

Where the first parentheses contain the module name, and the optional second pair contains the specifically imported entities from the given module (separated by spaces). One line contains one module import.

Example:

```
import (Data.Map)
import (Data.List) (genericLength genericTake)
```

The Haskell implementation imports `Data.List` by default, because some of the generated functions use its functions.

### Namespace declarations

A namespace declaration consists of the namespace's name, a sort name, and optionally additional comma separated sort names (the environment of the namespace).

```
namespace NAMESPACENAME: SORTNAME[, SORTNAME]*
```

Example:
```
namespace TermVar: Term, Type
namespace TypeVar: Type
```

### Sort declarations

Sort declarations have the following structure:

- name, rewrite declaration
- context declarations
- constructor declarations
    + attribute assignments

#### Name, rewrite

```
sort SORTNAME [rewrite]
```

Declares a new sort. The optional rewrite keyword specifies whether the result of substitution functions for the given sort should be passed to an external rewrite function. The rewrite functions need to have the name `rewriteSORTNAME` and either be defined in the native code section or imported.

#### Context declarations

A sort can have multiple (or no) context attributes. These are declared after the sort name with the following syntax:

```
CTXTYPE CTXINSTANCE NAMESPACENAME
```

Where `CTXTYPE` can be `inh` for inherited and `syn` for synthesized contexts. `CTXINSTANCE` is the context instance's name, and `NAMESPACENAME` is the name of the namespace of the contained variables.

Example:
```
namespace TermVar: Term

sort Pat
    inh ictx TermVar
    syn sctx TermVar
```

#### Constructor declarations

Sorts can contain a number of constructor declarations. These follow the context declarations. A constructor declaration consists of a constructor name, parameter declarations, and context attribute assignments.

The parameter declarations can be of the following forms:
- List of a sort
- Foldable sort
- Regular sort
- Native type
- Binder parameter of a namespace

You can have zero or more parameters of each type, but the order of their declaration must correspond to the order in this list.

```
| CTORNAME [ (PARAM: [SORTNAME]) ]* [ (PARAM: FOLDNAME SORTNAME) ]* [ (PARAM: SORTNAME) ]* [ {NATIVETYPE} ]* [ [BINDPARAM: NAMESPACENAME] ]
```

The final part of the constructor declaration is the context attribute assignments. Zero or more of them can follow the parameter list in new lines.

```
    PARAM.CTXINSTANCE = PARAM.CTXINSTANCE[, PARAM]
```

Where `PARAM` can be one of the constructor parameters or `lhs` which represents the constructor's context. You can optionally also append a parameter to the assigned context instance.

Example:

```
namespace TermVar: Term

sort Term
    inh ctx TermVar
    | TmAbs (x: Term) (t: Type) [z: TermVar]
        x.ctx = lhs.ctx, z
```

### Native code

After the sort declarations you can include code written in the target language. This needs to be preceded by the `NativeCode` keyword. Everything after this keyword will be copied verbatim to the output module.

For example, if we want to generate a Haskell module, we can put the following in the language specification:

```
[import declarations...]
[namespace declarations...]
[sort declarations...]

NativeCode

rewriteCoercion :: Coercion -> Coercion
rewriteCoercion (CoTypeVar ty)    = rewriteTypeToCoercion ty
rewriteCoercion (CoArrow co1 co2) = CoArrow (rewriteCoercion co1) (rewriteCoercion co2)
```
