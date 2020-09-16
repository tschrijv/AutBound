# AutBound: Code generator for abstract syntax trees

## Generated data structures and functions

### Data types

- For each declared sort in the specification, the corresponding data type will
  be created with the required parameters as constructor parameters. If a given
  constructor contains a binding parameter, and the generated code uses string
  variable representations, the binder will become the first constructor
  parameter in the generated type.
- A data type for the variables will also be created (`HNat` for the De Bruijn,
  `Variable` for the string representation) which has different constructors for
  each namespace declaration.

### Functions

- Mapping functions: mapping functions are created for each sort that has access
  to variables either by having a variable constructor, or a context instance of
  a sort that has access to variables (recursive case). Mapping functions take
  the following parameters: functions for each context instance sort with
  signature `[Variable] -> SORT -> SORT`, which get called if a variable of that
  sort is encountered, a variable list `c`, and the constructor of the given
  sort. An example signature for a `Term` sort with a variable constructor might
  be: `termmap :: ([Variable] -> Term -> Term) -> [Variable] -> Term -> Term`.
  The variable lists in both the map call and the parameter functions contain
  the active binders for the current context.
- Free variable functions: free variable functions are also created for sorts
  with variable access. These functions have the signature
  `[Variable] -> SORT -> [Variable]`. The functions takes the list of bound
  parameters and the term as parameters, and returns the list of free variables
  in the term.
- Substitution functions: substitution functions for sorts with variable access
  are generated for each context instance in the sort. They have the signature
  `sortCtxSortSubstitute :: Variable -> CTXSORT -> SORT -> SORT` where the free
  occurrences of the variable are replaced with the expression of type `CTXSORT`
  in the term of type `SORT`.

## Usage

The executable can be used from the command line with the following arguments:

```
autbound SOURCE_FILE OUTPUT_LANGUAGE VARIABLE_TYPE OUTPUT_NAME
```

For example, if we want to generate a Haskell module called `FCoBase` from the
FCo specification, using string-based variables, we would issue the command:

```
autbound "Specifications/FCo.txt" Haskell String FCoBase
```

This will generate the file `FCoBase.hs` in the current directory.

The following options are currently available:
- `OUTPUT_LANGUAGE`: `Haskell`, `OCaml`
- `VARIABLE_TYPE`: `DeBruijn`, `String`

## Language descriptions

Language descriptions are simple text files. They consist of four different
parts:

- Import declarations
- Namespace declarations
- Sort declarations
- Relation declarations
- Native code

None of these sections are mandatory, but their order is fixed.

For examples of language descriptions, see the `Specifications` directory.

### Import declarations

If your native code uses other modules, you can declare the import statements
with the following syntax at the top of your language description:

```
import (MODULE_NAME) [ ( ENTITY [ ENTITY]* ) ]
```

Where the first parentheses contain the module name, and the optional second
pair contains the specifically imported entities from the given module
(separated by spaces). One line contains one module import.

Example:

```
import (Data.Map)
import (Data.List) (genericLength genericTake)
```

The Haskell implementation imports `Data.List` by default, because some of the
generated functions use its functions.

### Namespace declarations

A namespace declaration consists of the namespace's name and the associated sort
name.

```
namespace NAMESPACENAME: SORTNAME
```

Example:
```
namespace TermVar: Term
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

Declares a new sort. The optional rewrite keyword specifies whether the result
of substitution functions for the given sort should be passed to an external
rewrite function. The rewrite functions need to have the name `rewriteSORTNAME`
and either be defined in the native code section or imported.

#### Context declarations

A sort can have multiple (or no) context attributes. These are declared after
the sort name with the following syntax:

```
CTXTYPE CTXINSTANCE NAMESPACENAME
```

Where `CTXTYPE` can be `inh` for inherited and `syn` for synthesized contexts.
`CTXINSTANCE` is the context instance's name, and `NAMESPACENAME` is the name
of the namespace of the contained variables.

Example:
```
namespace TermVar: Term

sort Pat
    inh ictx TermVar
    syn sctx TermVar
```

#### Constructor declarations

Sorts can contain a number of constructor declarations. These follow the context
declarations. A constructor declaration consists of a constructor name,
parameter declarations, and context attribute assignments.

The parameter declarations can be of the following forms:
- List of a sort
- Foldable sort
- Regular sort
- Native type
- Binder parameter of a namespace

You can have zero or more parameters of each type, but the order of their
declaration must correspond to the order in this list.

```
| CTORNAME [ (PARAM: [SORTNAME]) ]* [ (PARAM: FOLDNAME SORTNAME) ]* [ (PARAM: SORTNAME) ]* [ {NATIVETYPE} ]* [ [BINDPARAM: NAMESPACENAME] ]
```

The final part of the constructor declaration is the context attribute
assignments. Zero or more of them can follow the parameter list in new lines.

```
    PARAM.CTXINSTANCE = PARAM.CTXINSTANCE[, PARAM]
```

Where `PARAM` can be one of the constructor parameters or `lhs` which represents
the constructor's context. You can optionally also append a parameter to the
assigned context instance.

Example:

```
namespace TermVar: Term

sort Term
    inh ctx TermVar
    | TmAbs (x: Term) (t: Type) [z: TermVar]
        x.ctx = lhs.ctx, z
```

### Relation declarations

The relation section starts with the `Relations` keyword.
A relation complies with the following syntax:
 ```
Relation ::= 					relations:
		TypeSignature RelationBody+	   		typesignature and one or more relation bodies

TypeSignature ::= 				typesignatures:
		N : Type -> RelationType	   		name, types of input parameters and kind of relation
	
Type ::=					types:
		Empty				   		empty type
		S -> Type			   		sort followed by more types
		
RelationType ::=				types of relations:
		o				   		clause type

RelationBody ::= 				body of the relation:
		Judgement.			   		judgement without conditions
		Judgement :- Judgement+.	   		judgement with one or more conditions
		
Judgement ::=					judgements:
		N Argument*			   		relation with its parameters

Argument ::=					arguments:
		A				   		metavariable
		C Argument*			   		constructor sort with its parameters
		Argument[x -> Argument]		   		substitution
 ```
 where `N` is the name of a relation, `S` is the name of an existing sort, `C` is a constructor of a sort, `x` is a variable name and `A` is a metavariable.

 Example for the STLCProd specification: 
 ```
 value : Term -> o
 value (Abs x t).

 opsem : Term -> Term -> o
 opsem (App T1 T2) (App T1' T2) :- opsem T1 T1'.
 opsem (App V T) (App V T') :- value V, opsem T T'.
 opsem (App (Abs x T1) V2) (T1[x -> V2]).
 ```
 The example above declares two relations: `value` and `opsem`. `value` is a relation with one argument and no conditions. `opsem` is more complicated: it consists of three clauses inside the relation, the first two have conditions and the third contains a substitution as its second argument.


### Native code

After the relation declarations you can include code written in the target language.
This needs to be preceded by the `NativeCode` keyword. Everything after this
keyword will be copied verbatim to the output module.

For example, if we want to generate a Haskell module, we can put the following
in the language specification:

```
[import declarations...]
[namespace declarations...]
[sort declarations...]

NativeCode

rewriteCoercion :: Coercion -> Coercion
rewriteCoercion (CoTypeVar ty)    = rewriteTypeToCoercion ty
rewriteCoercion (CoArrow co1 co2) = CoArrow (rewriteCoercion co1) (rewriteCoercion co2)
```
