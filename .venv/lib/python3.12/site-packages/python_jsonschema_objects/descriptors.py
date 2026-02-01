from python_jsonschema_objects import util, validators, wrapper_types
from python_jsonschema_objects.classbuilder import ProtocolBase, TypeProxy, TypeRef


class AttributeDescriptor(object):
    """Provides property access for constructed class properties"""

    def __init__(self, prop, info, desc=""):
        self.prop = prop
        self.info = info
        self.desc = desc

    def __doc__(self):
        return self.desc

    def __get__(self, obj, owner=None):
        if obj is None and owner is not None:
            return self

        try:
            return obj._properties[self.prop]
        except KeyError:
            raise AttributeError("No such attribute")

    def __set__(self, obj, val):
        info = self.info
        if isinstance(info["type"], (list, tuple)):
            ok = False
            errors = []
            type_checks = []

            for typ in info["type"]:
                if not isinstance(typ, dict):
                    type_checks.append(typ)
                    continue
                typ = next(
                    t for n, t in validators.SCHEMA_TYPE_MAPPING if typ["type"] == n
                )
                if typ is None:
                    typ = type(None)
                if isinstance(typ, (list, tuple)):
                    type_checks.extend(typ)
                else:
                    type_checks.append(typ)

            for typ in type_checks:
                if not isinstance(typ, TypeProxy) and isinstance(val, typ):
                    ok = True
                    break
                elif hasattr(typ, "isLiteralClass"):
                    try:
                        validator = typ(val)
                        validator.validate()
                    except Exception as e:
                        errors.append("Failed to coerce to '{0}': {1}".format(typ, e))
                        pass
                    else:
                        ok = True
                        break
                elif util.safe_issubclass(typ, ProtocolBase):
                    # Force conversion- thus the val rather than validator assignment.
                    try:
                        val = typ(**val)
                        val.validate()
                    except Exception as e:
                        errors.append("Failed to coerce to '{0}': {1}".format(typ, e))
                        pass
                    else:
                        ok = True
                        break
                elif util.safe_issubclass(typ, wrapper_types.ArrayWrapper):
                    try:
                        val = typ(val)
                        val.validate()
                    except Exception as e:
                        errors.append("Failed to coerce to '{0}': {1}".format(typ, e))
                        pass
                    else:
                        ok = True
                        break
                elif isinstance(typ, TypeProxy):
                    try:
                        # Handle keyword expansion according to expected types. Using
                        # keywords like oneOf, value can be an object, array or literal.
                        if isinstance(val, dict):
                            val = typ(**val)
                        else:
                            val = typ(val)
                        val.validate()
                    except Exception as e:
                        errors.append("Failed to coerce to '{0}': {1}".format(typ, e))
                        pass
                    else:
                        ok = True
                        break

            if not ok:
                errstr = "\n".join(errors)
                raise validators.ValidationError(
                    "Object must be one of {0}: \n{1}".format(info["type"], errstr)
                )

        elif info["type"] == "array":
            val = info["validator"](val)
            val.validate()

        elif util.safe_issubclass(info["type"], wrapper_types.ArrayWrapper):
            # An array type may have already been converted into an ArrayValidator.
            val = info["type"](val)
            val.validate()

        elif getattr(info["type"], "isLiteralClass", False) is True:
            if not isinstance(val, info["type"]):
                validator = info["type"](val)
                validator.validate()
                if validator._value is not None:
                    # This allows setting of default Literal values.
                    val = validator

        elif util.safe_issubclass(info["type"], ProtocolBase):
            if not isinstance(val, info["type"]):
                val = info["type"](**val)

            val.validate()

        elif isinstance(info["type"], TypeProxy):
            if isinstance(val, dict):
                val = info["type"](**val)
            else:
                val = info["type"](val)

        elif isinstance(info["type"], TypeRef):
            if not isinstance(val, info["type"].ref_class):
                val = info["type"](**val)

            val.validate()

        elif info["type"] is None:
            # This is the null value
            if val is not None:
                raise validators.ValidationError("None is only valid value for null")

        else:
            raise TypeError("Unknown object type: '{0}'".format(info["type"]))

        obj._properties[self.prop] = val

    def __delete__(self, obj):
        prop = self.prop
        if prop in obj.__required__:
            raise AttributeError("'%s' is required" % prop)
        else:
            obj._properties[prop] = None
