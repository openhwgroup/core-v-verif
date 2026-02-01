import collections
import logging
import re


from python_jsonschema_objects import util, validators, wrapper_types
from python_jsonschema_objects.literals import MakeLiteral

logger = logging.getLogger(__name__)

PatternDef = collections.namedtuple("PatternDef", "pattern schema_type")


class ExtensibleValidator(object):
    def __init__(self, name, schemadef, builder):
        import python_jsonschema_objects.classbuilder as cb

        self._pattern_types = []
        self._additional_type = True

        addlProp = schemadef.get("additionalProperties", True)

        if addlProp is False:
            self._additional_type = False
        elif addlProp is True:
            self._additional_type = True
        else:
            if "$ref" in addlProp:
                typ = builder.resolve_type(addlProp["$ref"], name)
            else:
                uri = "{0}/{1}_{2}".format(
                    name, "<additionalProperties>", "<anonymous>"
                )
                builder.resolved[uri] = builder.construct(
                    uri, addlProp, (cb.ProtocolBase,)
                )
                typ = builder.resolved[uri]

            self._additional_type = typ

        for pattern, typedef in schemadef.get("patternProperties", {}).items():
            if "$ref" in typedef:
                typ = builder.resolve_type(typedef["$ref"], name)
            else:
                uri = "{0}/{1}_{2}".format(name, "<patternProperties>", pattern)

                builder.resolved[uri] = builder.construct(
                    uri, typedef, (cb.ProtocolBase,)
                )
                typ = builder.resolved[uri]

            self._pattern_types.append(
                PatternDef(pattern=re.compile(pattern), schema_type=typ)
            )

    def _make_type(self, typ, val):
        import python_jsonschema_objects.classbuilder as cb

        if getattr(typ, "isLiteralClass", None) is True:
            return typ(val)

        if util.safe_issubclass(typ, cb.ProtocolBase):
            return typ(**val)

        if util.safe_issubclass(typ, wrapper_types.ArrayWrapper):
            return typ(val)

        if isinstance(typ, cb.TypeProxy):
            if isinstance(val, dict):
                val = typ(**val)
            else:
                val = typ(val)
            return val

        raise validators.ValidationError(
            "additionalProperty type {0} was neither a literal "
            "nor a schema wrapper: {1}".format(typ, val)
        )

    def instantiate(self, name, val):
        import python_jsonschema_objects.classbuilder as cb

        for p in self._pattern_types:
            if p.pattern.search(name):
                logger.debug(
                    "Found patternProperties match: %s %s" % (p.pattern.pattern, name)
                )
                return self._make_type(p.schema_type, val)

        if self._additional_type is True:
            valtype = [
                k
                for k, t in validators.SCHEMA_TYPE_MAPPING
                if t is not None and isinstance(val, t)
            ]
            valtype = valtype[0]
            return MakeLiteral(name, valtype, val)

        elif isinstance(self._additional_type, (type, cb.TypeProxy)):
            return self._make_type(self._additional_type, val)

        raise validators.ValidationError(
            "additionalProperties not permitted " "and no patternProperties specified"
        )
