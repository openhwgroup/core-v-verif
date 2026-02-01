[![Build](https://github.com/cwacek/python-jsonschema-objects/actions/workflows/pythonpackage.yml/badge.svg?branch=master)](https://github.com/cwacek/python-jsonschema-objects/actions/workflows/pythonpackage.yml)

## What

python-jsonschema-objects provides an *automatic* class-based
binding to JSON Schemas for use in python. See [Draft Schema
Support](#draft-schema-support) to see supported keywords

For example, given the following schema:

``` schema
{
    "title": "Example Schema",
    "type": "object",
    "properties": {
        "firstName": {
            "type": "string"
        },
        "lastName": {
            "type": "string"
        },
        "age": {
            "description": "Age in years",
            "type": "integer",
            "minimum": 0
        },
        "dogs": {
            "type": "array",
            "items": {"type": "string"},
            "maxItems": 4
        },
        "address": {
            "type": "object",
            "properties": {
                "street": {"type": "string"},
                "city": {"type": "string"},
                "state": {"type": "string"}
                },
            "required":["street", "city"]
            },
        "gender": {
            "type": "string",
            "enum": ["male", "female"]
        },
        "deceased": {
            "enum": ["yes", "no", 1, 0, "true", "false"]
            }
    },
    "required": ["firstName", "lastName"]
}
```

jsonschema-objects can generate a class based binding. Assume
here that the schema above has been loaded in a variable called
`examples`:

``` python
>>> import python_jsonschema_objects as pjs
>>> builder = pjs.ObjectBuilder(examples['Example Schema'])
>>> ns = builder.build_classes()
>>> Person = ns.ExampleSchema
>>> james = Person(firstName="James", lastName="Bond")
>>> james.lastName
<Literal<str> Bond>
>>> james.lastName == "Bond"
True
>>> james
<example_schema address=None age=None deceased=None dogs=None firstName=<Literal<str> James> gender=None lastName=<Literal<str> Bond>>

```

Validations will also be applied as the object is manipulated.

``` python
>>> james.age = -2  # doctest: +IGNORE_EXCEPTION_DETAIL
Traceback (most recent call last):
    ...
ValidationError: -2 is less than 0

>>> james.dogs= ["Jasper", "Spot", "Noodles", "Fido", "Dumbo"]  # doctest: +IGNORE_EXCEPTION_DETAIL
Traceback (most recent call last):
    ...
ValidationError: ["Jasper", "Spot", "Noodles", "Fido", "Dumbo"]  has too many elements. Wanted 4.

```

The object can be serialized out to JSON. Options are passed
through to the standard library JSONEncoder object.

``` python
>>> james.serialize(sort_keys=True)
'{"firstName": "James", "lastName": "Bond"}'

```

## Why

Ever struggled with how to define message formats? Been
frustrated by the difficulty of keeping documentation and message
definition in lockstep? Me too.

There are lots of tools designed to help define JSON object
formats, foremost among them [JSON Schema](http://json-schema.org).
JSON Schema allows you to define JSON object formats, complete
with validations.

However, JSON Schema is language agnostic. It validates encoded
JSON directly - using it still requires an object binding in
whatever language we use. Often writing the binding is just as
tedious as writing the schema itself.

This avoids that problem by auto-generating classes, complete
with validation, directly from an input JSON schema. These
classes can seamlessly encode back and forth to JSON valid
according to the schema.

## Fully Functional Literals

Literal values are wrapped when constructed to support validation
and other schema-related operations. However, you can still use
them just as you would other literals.

``` python
>>> import python_jsonschema_objects as pjs
>>> builder = pjs.ObjectBuilder(examples['Example Schema'])
>>> ns = builder.build_classes()
>>> Person = ns.ExampleSchema
>>> james = Person(firstName="James", lastName="Bond")
>>> str(james.lastName)
'Bond'
>>> james.lastName += "ing"
>>> str(james.lastName)
'Bonding'
>>> james.age = 4
>>> james.age - 1
3
>>> 3 + james.age
7
>>> james.lastName / 4
Traceback (most recent call last):
    ...
TypeError: unsupported operand type(s) for /: 'str' and 'int'

```

## Accessing Generated Objects

Sometimes what you really want to do is define a couple
of different objects in a schema, and then be able to use
them flexibly.

Any object built as a reference can be obtained from the top
level namespace. Thus, to obtain multiple top level classes,
define them separately in a definitions structure, then simply
make the top level schema refer to each of them as a `oneOf`.

Other classes identified during the build process will also be
available from the top level object. However, if you pass `named_only`
to the build_classes call, then only objects with a `title` will be
included in the output namespace.

Finally, by default, the names in the returned namespace are transformed
by passing them through a camel case function. If you want to have names unchanged,
pass `standardize_names=False` to the build call.

The schema and code example below show how this works.

``` schema
{
    "title": "MultipleObjects",
    "id": "foo",
    "type": "object",
    "oneOf":[
            {"$ref": "#/definitions/ErrorResponse"},
            {"$ref": "#/definitions/VersionGetResponse"}
            ],
    "definitions": {
        "ErrorResponse": {
            "title": "Error Response",
            "id": "Error Response",
            "type": "object",
            "properties": {
                "message": {"type": "string"},
                "status": {"type": "integer"}
            },
            "required": ["message", "status"]
        },
        "VersionGetResponse": {
            "title": "Version Get Response",
            "type": "object",
            "properties": {
                "local": {"type": "boolean"},
                "version": {"type": "string"}
            },
            "required": ["version"]
        }
    }
}
```

``` python
>>> builder = pjs.ObjectBuilder(examples["MultipleObjects"])
>>> classes = builder.build_classes()
>>> [str(x) for x in dir(classes)]
['ErrorResponse', 'Local', 'Message', 'Multipleobjects', 'Status', 'Version', 'VersionGetResponse']
>>> classes = builder.build_classes(named_only=True, standardize_names=False)
>>> [str(x) for x in dir(classes)]
['Error Response', 'MultipleObjects', 'Version Get Response']
>>> classes = builder.build_classes(named_only=True)
>>> [str(x) for x in dir(classes)]
['ErrorResponse', 'Multipleobjects', 'VersionGetResponse']

```


## Supported Operators

### $ref

The `$ref` operator is supported in nearly all locations, and
dispatches the actual reference resolution to the
`referencing.Registry` resolver.

This example shows using the memory URI (described in more detail
below) to create a wrapper object that is just a string literal.

``` schema
{
    "title": "Just a Reference",
    "$ref": "memory:Address"
}
```

```python
>>> builder = pjs.ObjectBuilder(examples['Just a Reference'], resolved=examples)
>>> ns = builder.build_classes()
>>> ns.JustAReference('Hello')
<Literal<str> Hello>

```

#### Circular References

Circular references are not a good idea, but they're supported
anyway via lazy loading (as much as humanly possible).

Given the crazy schema below, we can actually generate these
classes.

```schema
{
    "title": "Circular References",
    "id": "foo",
    "type": "object",
    "oneOf":[
            {"$ref": "#/definitions/A"},
            {"$ref": "#/definitions/B"}
    ],
    "definitions": {
        "A": {
            "type": "object",
            "properties": {
                "message": {"type": "string"},
                "reference": {"$ref": "#/definitions/B"}
            },
            "required": ["message"]
        },
        "B": {
            "type": "object",
            "properties": {
                "author": {"type": "string"},
                "oreference": {"$ref": "#/definitions/A"}
            },
            "required": ["author"]
        }
    }
}
```

We can instantiate objects that refer to each other.

```
>>> builder = pjs.ObjectBuilder(examples['Circular References'])
>>> klasses = builder.build_classes()
>>> a = klasses.A()
>>> b = klasses.B()
>>> a.message= 'foo'
>>> a.reference = b  # doctest: +IGNORE_EXCEPTION_DETAIL 
Traceback (most recent call last):
    ...
ValidationError: '[u'author']' are required attributes for B
>>> b.author = "James Dean"
>>> a.reference = b
>>> a
<A message=<Literal<str> foo> reference=<B author=<Literal<str> James Dean> oreference=None>>

```

#### The "memory:" URI

**"memory:" URIs are deprecated (although they still work). Load resources into a
`referencing.Registry` instead and pass those in**

The ObjectBuilder can be passed a dictionary specifying
'memory' schemas when instantiated. This will allow it to
resolve references where the referenced schemas are retrieved
out of band and provided at instantiation.

For instance, given the following schemas:

``` schema
{
    "title": "Address",
    "type": "string"
}
```

``` schema
{
    "title": "AddlPropsAllowed",
    "type": "object",
    "additionalProperties": true
}
```

``` schema
{
    "title": "Other",
    "type": "object",
    "properties": {
        "MyAddress": {"$ref": "memory:Address"}
    },
    "additionalProperties": false
}
```

The ObjectBuilder can be used to build the "Other" object by
passing in a definition for "Address".

``` python
>>> builder = pjs.ObjectBuilder(examples['Other'], resolved={"Address": {"type":"string"}})
>>> builder.validate({"MyAddress": '1234'})
>>> ns = builder.build_classes()
>>> thing = ns.Other()
>>> thing
<other MyAddress=None>
>>> thing.MyAddress = "Franklin Square"
>>> thing
<other MyAddress=<Literal<str> Franklin Square>>
>>> thing.MyAddress = 423  # doctest: +IGNORE_EXCEPTION_DETAIL
Traceback (most recent call last):
    ...
ValidationError: 432 is not a string

```

### oneOf

Generated wrappers can properly deserialize data
representing 'oneOf' relationships, so long as the candidate
schemas are unique.

``` schema
{
    "title": "Age",
    "type": "integer"
}

```

``` schema
{
    "title": "OneOf",
    "type": "object",
    "properties": {
        "MyData": { "oneOf":[
            {"$ref": "memory:Address"},
            {"$ref": "memory:Age"}
            ]
        }
    },
    "additionalProperties": false
}
```
``` schema
{
    "title": "OneOfBare",
    "type": "object",
    "oneOf":[
            {"$ref": "memory:Other"},
            {"$ref": "memory:Example Schema"}
            ],
    "additionalProperties": false
}
```

## Installation

    pip install python_jsonschema_objects

## Tests

Tests are managed using the excellent Tox. Simply `pip install
tox`, then `tox`.

## Draft Keyword Support

Most of draft-4 is supported, so only exceptions are noted
in the table. Where a keyword functionality changed between
drafts, the version that is supported is noted.

The library will warn (but not throw an exception) if you give
it an unsupported `$schema`

| Keyword | supported | version |
| --------| -----------| --------- |
| $id     | true   | draft-6      |
| propertyNames | false   | |
| contains    | false   | |
| const | false   |      |
| required | true   | draft-4 |
| examples | false |       |
| format | false |       |


## Changelog

*Please refer to Github releases for up to date changelogs.*

**0.0.18**

+ Fix assignment to schemas defined using 'oneOf'
+ Add sphinx documentation and support for readthedocs

0.0.16 - Fix behavior of exclusiveMinimum and exclusiveMaximum
validators so that they work properly.

0.0.14 - Roll in a number of fixes from Github contributors,
including fixes for oneOf handling, array validation, and Python
3 support.

0.0.13 - Lazily build object classes. Allows low-overhead use
of jsonschema validators.

0.0.12 - Support "true" as a value for 'additionalProperties'

0.0.11 - Generated wrappers can now properly deserialize data
representing 'oneOf' relationships, so long as the candidate
schemas are unique.

0.0.10 - Fixed incorrect checking of enumerations which
previously enforced that all enumeration values be of the same
type.

0.0.9 - Added support for 'memory:' schema URIs, which can be
used to reference externally resolved schemas.

0.0.8 - Fixed bugs that occurred when the same class was read
from different locations in the schema, and thus had a different
URI

0.0.7 - Required properties containing the '@' symbol no longer
cause `build_classes()` to fail.

0.0.6 - All literals now use a standardized LiteralValue type.
Array validation actually coerces element types. `as_dict` can
translate objects to dictionaries seamlessly.

0.0.5 - Improved validation for additionalItems (and tests to
match). Provided dictionary-syntax access to object properties
and iteration over properties.

0.0.4 - Fixed some bugs that only showed up under specific schema
layouts, including one which forced remote lookups for
schema-local references.

0.0.3b - Fixed ReStructuredText generation

0.0.3 - Added support for other array validations (minItems,
maxItems, uniqueItems).

0.0.2 - Array item type validation now works. Specifying 'items',
will now enforce types, both in the tuple and list syntaxes.

0.0.1 - Class generation works, including 'oneOf' and 'allOf'
relationships. All basic validations work.
