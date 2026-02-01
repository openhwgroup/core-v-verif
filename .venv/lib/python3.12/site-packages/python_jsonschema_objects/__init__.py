__all__ = ["ObjectBuilder", "markdown_support", "ValidationError"]

import codecs
import copy
import json
import logging
import os.path
import warnings
from typing import Optional
import typing

import inflection
import jsonschema
import referencing.jsonschema
import referencing.retrieval
import referencing._core
from referencing import Registry, Resource

import python_jsonschema_objects.classbuilder as classbuilder
import python_jsonschema_objects.markdown_support
import python_jsonschema_objects.util
from python_jsonschema_objects.validators import ValidationError

logger = logging.getLogger(__name__)

__all__ = ["ObjectBuilder", "markdown_support", "ValidationError"]

FILE = __file__

SUPPORTED_VERSIONS = (
    "http://json-schema.org/draft-03/schema",
    "http://json-schema.org/draft-04/schema",
)


class ObjectBuilder(object):
    def __init__(
        self,
        schema_uri: typing.Union[typing.AnyStr, typing.Mapping],
        resolved: typing.Dict[typing.AnyStr, typing.Mapping] = {},
        registry: Optional[referencing.Registry] = None,
        resolver: Optional[referencing.typing.Retrieve] = None,
        specification_uri: Optional[str] = None,
    ):
        if isinstance(schema_uri, str):
            uri = os.path.normpath(schema_uri)
            self.basedir = os.path.dirname(uri)
            with codecs.open(uri, "r", "utf-8") as fin:
                self.schema = json.loads(fin.read())
        else:
            self.schema = schema_uri
            uri = os.path.normpath(FILE)
            self.basedir = os.path.dirname(uri)

        if (
            "$schema" in self.schema
            and self.schema["$schema"].rstrip("#") not in SUPPORTED_VERSIONS
        ):
            warnings.warn(
                "Schema version {} not recognized. Some "
                "keywords and features may not be supported.".format(
                    self.schema["$schema"]
                )
            )

        if registry is not None:
            if not isinstance(registry, referencing.Registry):
                raise TypeError("registry must be a Registry instance")

            if resolver is not None:
                raise AttributeError(
                    "Cannot specify both registry and resolver. If you provide your own registry, pass the resolver "
                    "directly to that"
                )
            self.registry = registry
        else:
            if resolver is not None:

                def file_and_memory_handler(uri):
                    if uri.startswith("file:"):
                        return Resource.from_contents(self.relative_file_resolver(uri))
                    return resolver(uri)

                self.registry = Registry(retrieve=file_and_memory_handler)
            else:

                def file_and_memory_handler(uri):
                    if uri.startswith("file:"):
                        return Resource.from_contents(self.relative_file_resolver(uri))
                    raise RuntimeError(
                        "No remote resource resolver provided. Cannot resolve {}".format(
                            uri
                        )
                    )

                self.registry = Registry(retrieve=file_and_memory_handler)

        if "$schema" not in self.schema:
            warnings.warn(
                "Schema version not specified. Defaulting to {}".format(
                    specification_uri or "http://json-schema.org/draft-04/schema"
                )
            )
            updated = {
                "$schema": specification_uri or "http://json-schema.org/draft-04/schema"
            }
            updated.update(self.schema)
            self.schema = updated

        schema = Resource.from_contents(self.schema)
        if schema.id() is None:
            warnings.warn("Schema id not specified. Defaulting to 'self'")
            updated = {"$id": "self", "id": "self"}
            updated.update(self.schema)
            self.schema = updated
            schema = Resource.from_contents(self.schema)

        self.registry = self.registry.with_resource("", schema)

        if len(resolved) > 0:
            warnings.warn(
                "Use of 'memory:' URIs is deprecated. Provide a registry with properly resolved references "
                "if you want to resolve items externally.",
                DeprecationWarning,
            )
        for uri, contents in resolved.items():
            from referencing.jsonschema import specification_with

            specification = specification_with(
                specification_uri or self.schema["$schema"]
            )
            self.registry = self.registry.with_resource(
                "memory:" + uri,
                referencing.Resource.from_contents(contents, specification),
            )

        validatorClass = jsonschema.validators.validator_for(
            {"$schema": specification_uri or self.schema["$schema"]}
        )

        meta_validator = validatorClass(
            validatorClass.META_SCHEMA, registry=self.registry
        )
        meta_validator.validate(self.schema)
        self.validator = validatorClass(self.schema, registry=self.registry)

        self._classes = None
        self._resolved = None

    @property
    def resolver(self) -> referencing._core.Resolver:
        return self.registry.resolver()

    @property
    def schema(self):
        try:
            return copy.deepcopy(self._schema)
        except AttributeError:
            raise ValidationError("No schema provided")

    @schema.setter
    def schema(self, val):
        setattr(self, "_schema", val)

    @property
    def classes(self):
        if self._classes is None:
            self._classes = self.build_classes()
        return self._classes

    def get_class(self, uri):
        if self._resolved is None:
            self._classes = self.build_classes()
        return self._resolved.get(uri, None)

    def relative_file_resolver(self, uri):
        path = os.path.join(self.basedir, uri[8:])
        with codecs.open(path, "r", "utf-8") as fin:
            result = json.loads(fin.read())
        return result

    def validate(self, obj):
        try:
            return self.validator.validate(obj)
        except jsonschema.ValidationError as e:
            raise ValidationError(e)

    def build_classes(
        self,
        strict=False,
        named_only=False,
        standardize_names=True,
        any_of: typing.Optional[typing.Literal["use-first"]] = None,
    ):
        """
        Build all of the classes named in the JSONSchema.

        Class names will be transformed using inflection by default, so names
        with spaces in the schema will be camelcased, while names without
        spaces will have internal capitalization dropped. Thus "Home Address"
        becomes "HomeAddress", while "HomeAddress" becomes "Homeaddress". To
        disable this behavior, pass standardize_names=False, but be aware that
        accessing names with spaces from the namespace can be problematic.

        Args:
            strict: (bool) use this to validate required fields while creating the class
            named_only: (bool) If true, only properties with an actual title attribute
                will be included in the resulting namespace (although all will be
                generated).
            standardize_names: (bool) If true (the default), class names will be
                transformed by camel casing
            any_of: (literal) If not set to None, defines the way anyOf clauses are resolved:
                - 'use-first': Generate to the first matching schema in the list under the anyOf
                - None: default behavior, anyOf is not supported in the schema

        Returns:
            A namespace containing all the generated classes

        """
        opts = {"strict": strict, "any_of": any_of}
        builder = classbuilder.ClassBuilder(self.resolver, opts)
        for nm, defn in self.schema.get("definitions", {}).items():
            resolved = self.resolver.lookup("#/definitions/" + nm)
            uri = python_jsonschema_objects.util.resolve_ref_uri(
                self.resolver._base_uri, "#/definitions/" + nm
            )
            builder.construct(uri, resolved.contents)

        if standardize_names:
            name_transform = lambda t: inflection.camelize(
                inflection.parameterize(str(t), "_")
            )
        else:
            name_transform = lambda t: t

        nm = self.schema["title"] if "title" in self.schema else self.schema["$id"]
        nm = inflection.parameterize(str(nm), "_")

        builder.construct(nm, self.schema)
        self._resolved = builder.resolved

        classes = {}
        for uri, klass in builder.resolved.items():
            title = getattr(klass, "__title__", None)
            if title is not None:
                classes[name_transform(title)] = klass
            elif not named_only:
                classes[name_transform(uri.split("/")[-1])] = klass

        return python_jsonschema_objects.util.Namespace.from_mapping(classes)


if __name__ == "__main__":
    validator = ObjectBuilder("../../protocol/json/schema.json")

from . import _version

__version__ = _version.get_versions()["version"]
