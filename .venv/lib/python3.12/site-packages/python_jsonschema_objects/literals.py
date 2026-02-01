import functools
import operator


from python_jsonschema_objects import util, validators


def MakeLiteral(name, typ, value, **properties):
    properties.update({"type": typ})
    klass = type(
        str(name),
        tuple((LiteralValue,)),
        {
            "__propinfo__": {
                "__literal__": properties,
                "__default__": properties.get("default"),
            }
        },
    )

    return klass(value)


@functools.total_ordering
class LiteralValue(object):
    """Docstring for LiteralValue"""

    isLiteralClass = True

    def __init__(self, value, typ=None):
        """@todo: to be defined

        :value: @todo

        """
        if isinstance(value, LiteralValue):
            self._value = value._value
        else:
            self._value = value

        self.validate()

        constval = self.const()
        if constval is not None:
            self._value = constval

    def as_dict(self):
        return self.for_json()

    def for_json(self):
        return self._value

    @classmethod
    def default(cls):
        return cls.__propinfo__.get("__default__")

    @classmethod
    def const(cls):
        return cls.__propinfo__.get("__literal__", {}).get("const", None)

    @classmethod
    def propinfo(cls, propname):
        if propname not in cls.__propinfo__:
            return {}
        return cls.__propinfo__[propname]

    def serialize(self):
        self.validate()
        enc = util.ProtocolJSONEncoder()
        return enc.encode(self)

    def __repr__(self):
        return "<Literal<%s> %s>" % (self._value.__class__.__name__, str(self._value))

    def __str__(self):
        if isinstance(self._value, str):
            return self._value
        return str(self._value)

    def validate(self):
        info = self.propinfo("__literal__")

        # TODO: this duplicates logic in validators.ArrayValidator.check_items;
        # unify it.
        for param, paramval in sorted(
            info.items(), key=lambda x: x[0].lower() != "type"
        ):
            validator = validators.registry(param)
            if validator is not None:
                validator(paramval, self._value, info)

    def __eq__(self, other):
        if isinstance(other, LiteralValue):
            return self._value == other._value
        return self._value == other

    def __hash__(self):
        return hash(self._value)

    def __lt__(self, other):
        if isinstance(other, LiteralValue):
            return self._value < other._value
        return self._value < other

    def __int__(self):
        return int(self._value)

    def __float__(self):
        return float(self._value)

    def __bool__(self):
        return bool(self._value)

    __nonzero__ = __bool__


EXCLUDED_OPERATORS = set(
    util.CLASS_ATTRS
    + util.NEWCLASS_ATTRS
    + [
        "__name__",
        "__setattr__",
        "__getattr__",
        "__dict__",
        "__matmul__",
        "__imatmul__",
    ]
)


def dispatch_to_value(fn):
    def wrapper(self, other):
        return fn(self._value, other)
        pass

    return wrapper


""" This attaches all the literal operators to LiteralValue
 except for the reverse ones."""
for op in dir(operator):
    if op.startswith("__") and op not in EXCLUDED_OPERATORS:
        opfn = getattr(operator, op)
        setattr(LiteralValue, op, dispatch_to_value(opfn))


""" We also have to patch the reverse operators,
which aren't conveniently defined anywhere """
LiteralValue.__radd__ = lambda self, other: other + self._value
LiteralValue.__rsub__ = lambda self, other: other - self._value
LiteralValue.__rmul__ = lambda self, other: other * self._value
LiteralValue.__rtruediv__ = lambda self, other: other / self._value
LiteralValue.__rfloordiv__ = lambda self, other: other // self._value
LiteralValue.__rmod__ = lambda self, other: other % self._value
LiteralValue.__rdivmod__ = lambda self, other: divmod(other, self._value)
LiteralValue.__rpow__ = lambda self, other, modulo=None: pow(other, self._value, modulo)
LiteralValue.__rlshift__ = lambda self, other: other << self._value
LiteralValue.__rrshift__ = lambda self, other: other >> self._value
LiteralValue.__rand__ = lambda self, other: other & self._value
LiteralValue.__rxor__ = lambda self, other: other ^ self._value
LiteralValue.__ror__ = lambda self, other: other | self._value
