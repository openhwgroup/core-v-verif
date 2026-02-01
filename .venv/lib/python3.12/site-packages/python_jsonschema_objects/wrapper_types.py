import collections
import logging


from python_jsonschema_objects import util
from python_jsonschema_objects.util import lazy_format as fmt
from python_jsonschema_objects.validators import ValidationError, registry

logger = logging.getLogger(__name__)


class ArrayWrapper(collections.abc.MutableSequence):
    """A wrapper for array-like structures.

    This implements all of the array like behavior that one would want,
    with a dirty-tracking mechanism to avoid constant validation costs.
    """

    @property
    def strict(self):
        return getattr(self, "_strict_", False)

    def __len__(self):
        return len(self.data)

    def mark_or_revalidate(self):
        if self.strict:
            self.validate()
        else:
            self._dirty = True

    def __delitem__(self, index):
        self.data.pop(index)
        self.mark_or_revalidate()

    def insert(self, index, value):
        self.data.insert(index, value)
        self.mark_or_revalidate()

    def __setitem__(self, index, value):
        self.data[index] = value
        self.mark_or_revalidate()

    def __getitem__(self, idx):
        return self.typed_elems[idx]

    def __eq__(self, other):
        if isinstance(other, ArrayWrapper):
            return self.for_json() == other.for_json()
        else:
            return self.for_json() == other

    def __init__(self, ary):
        """Initialize a wrapper for the array

        Args:
            ary: (list-like, or ArrayWrapper)
        """

        """ Marks whether or not the underlying array has been modified """
        self._dirty = True

        """ Holds a typed copy of the array """
        self._typed = None

        if isinstance(ary, (list, tuple, collections.abc.Sequence)):
            self.data = ary
        else:
            raise TypeError("Invalid value given to array validator: {0}".format(ary))

        logger.debug(fmt("Initializing ArrayWrapper {} with {}", self, ary))

    @property
    def typed_elems(self):
        logger.debug(fmt("Accessing typed_elems of ArrayWrapper {} ", self))
        if self._typed is None or self._dirty is True:
            self.validate()

        return self._typed

    def __repr__(self):
        return "<%s=%s>" % (self.__class__.__name__, str(self.data))

    @classmethod
    def from_json(cls, jsonmsg):
        import json

        msg = json.loads(jsonmsg)
        obj = cls(msg)
        obj.validate()
        return obj

    def serialize(self):
        enc = util.ProtocolJSONEncoder()
        return enc.encode(self.typed_elems)

    def for_json(self):
        from python_jsonschema_objects import classbuilder

        out = []
        for item in self.typed_elems:
            if isinstance(
                item,
                (classbuilder.ProtocolBase, classbuilder.LiteralValue, ArrayWrapper),
            ):
                out.append(item.for_json())
            else:
                out.append(item)

        return out

    def validate(self):
        if self.strict or self._dirty:
            self.validate_items()
            self.validate_length()
            self.validate_uniqueness()
        return True

    def validate_uniqueness(self):
        if getattr(self, "uniqueItems", False) is True:
            testset = set(repr(item) for item in self.data)
            if len(testset) != len(self.data):
                raise ValidationError(
                    "{0} has duplicate elements, but uniqueness required".format(
                        self.data
                    )
                )

    def validate_length(self):
        if getattr(self, "minItems", None) is not None:
            if len(self.data) < self.minItems:
                raise ValidationError(
                    "{1} has too few elements. Wanted {0}.".format(
                        self.minItems, self.data
                    )
                )

        if getattr(self, "maxItems", None) is not None:
            if len(self.data) > self.maxItems:
                raise ValidationError(
                    "{1} has too many elements. Wanted {0}.".format(
                        self.maxItems, self.data
                    )
                )

    def validate_items(self):
        """Validates the items in the backing array, including
        performing type validation.

        Sets the _typed property and clears the dirty flag as a side effect

        Returns:
            The typed array
        """
        logger.debug(fmt("Validating {}", self))
        from python_jsonschema_objects import classbuilder

        if self.__itemtype__ is None:
            return

        type_checks = self.__itemtype__
        if not isinstance(type_checks, (tuple, list)):
            # We were given items = {'type': 'blah'}.
            # Thus ensure the type for all data.
            type_checks = [type_checks] * len(self.data)
        elif len(type_checks) > len(self.data):
            raise ValidationError(
                "{1} does not have sufficient elements to validate against {0}".format(
                    self.__itemtype__, self.data
                )
            )

        typed_elems = []
        for elem, typ in zip(self.data, type_checks):
            if isinstance(typ, dict):
                for param, paramval in typ.items():
                    validator = registry(param)
                    if validator is not None:
                        validator(paramval, elem, typ)
                typed_elems.append(elem)

            elif util.safe_issubclass(typ, classbuilder.LiteralValue):
                val = typ(elem)
                val.validate()
                typed_elems.append(val)
            elif util.safe_issubclass(typ, classbuilder.ProtocolBase):
                if not isinstance(elem, typ):
                    try:
                        if isinstance(elem, (str, int, float)):
                            val = typ(elem)
                        else:
                            val = typ(**elem)
                    except TypeError as e:
                        raise ValidationError(
                            "'{0}' is not a valid value for '{1}': {2}".format(
                                elem, typ, e
                            )
                        )
                else:
                    val = elem
                val.validate()
                typed_elems.append(val)

            elif util.safe_issubclass(typ, ArrayWrapper):
                val = typ(elem)
                val.validate()
                typed_elems.append(val)

            elif isinstance(typ, (classbuilder.TypeProxy, classbuilder.TypeRef)):
                try:
                    if isinstance(elem, (str, int, float)):
                        val = typ(elem)
                    elif isinstance(elem, classbuilder.LiteralValue):
                        val = typ(elem._value)
                    else:
                        val = typ(**elem)
                except TypeError as e:
                    raise ValidationError(
                        "'{0}' is not a valid value for '{1}': {2}".format(elem, typ, e)
                    )
                else:
                    val.validate()
                    typed_elems.append(val)

        self._dirty = False
        self._typed = typed_elems
        return typed_elems

    @staticmethod
    def create(name, item_constraint=None, **addl_constraints):
        """Create an array validator based on the passed in constraints.

        If item_constraint is a tuple, it is assumed that tuple validation
        is being performed. If it is a class or dictionary, list validation
        will be performed. Classes are assumed to be subclasses of ProtocolBase,
        while dictionaries are expected to be basic types ('string', 'number', ...).

        addl_constraints is expected to be key-value pairs of any of the other
        constraints permitted by JSON Schema v4.
        """
        logger.debug(
            fmt(
                "Constructing ArrayValidator with {} and {}",
                item_constraint,
                addl_constraints,
            )
        )
        from python_jsonschema_objects import classbuilder

        klassbuilder = addl_constraints.pop(
            "classbuilder", None
        )  # type: python_jsonschema_objects.classbuilder.ClassBuilder
        props = {}

        if item_constraint is not None:
            if isinstance(item_constraint, (tuple, list)):
                for i, elem in enumerate(item_constraint):
                    isdict = isinstance(elem, (dict,))
                    isklass = isinstance(elem, type) and util.safe_issubclass(
                        elem, (classbuilder.ProtocolBase, classbuilder.LiteralValue)
                    )

                    if not any([isdict, isklass]):
                        raise TypeError(
                            "Item constraint (position {0}) is not a schema".format(i)
                        )
            elif isinstance(
                item_constraint, (classbuilder.TypeProxy, classbuilder.TypeRef)
            ):
                pass
            elif util.safe_issubclass(item_constraint, ArrayWrapper):
                pass
            else:
                isdict = isinstance(item_constraint, (dict,))
                isklass = isinstance(item_constraint, type) and util.safe_issubclass(
                    item_constraint,
                    (classbuilder.ProtocolBase, classbuilder.LiteralValue),
                )

                if not any([isdict, isklass]):
                    raise TypeError("Item constraint is not a schema")

                if isdict and "$ref" in item_constraint:
                    if klassbuilder is None:
                        raise TypeError(
                            "Cannot resolve {0} without classbuilder".format(
                                item_constraint["$ref"]
                            )
                        )

                    item_constraint = klassbuilder.resolve_type(
                        item_constraint["$ref"], name
                    )

                elif isdict and item_constraint.get("type") == "array":
                    # We need to create a sub-array validator.
                    item_constraint = ArrayWrapper.create(
                        name + "#sub",
                        item_constraint=item_constraint["items"],
                        addl_constraints=item_constraint,
                    )
                elif isdict and "oneOf" in item_constraint:
                    # We need to create a TypeProxy validator.
                    uri = "{0}_{1}".format(name, "<anonymous_list_type>")
                    type_array = klassbuilder.construct_objects(
                        item_constraint["oneOf"], uri
                    )

                    item_constraint = classbuilder.TypeProxy(type_array)

                elif isdict and item_constraint.get("type") == "object":
                    # We need to create a ProtocolBase object for this
                    # anonymous definition.
                    uri = "{0}_{1}".format(name, "<anonymous_list_type>")
                    item_constraint = klassbuilder.construct(uri, item_constraint)

        props["__itemtype__"] = item_constraint

        strict = addl_constraints.pop("strict", False)
        props["_strict_"] = strict
        props.update(addl_constraints)

        validator = type(str(name), (ArrayWrapper,), props)

        return validator
