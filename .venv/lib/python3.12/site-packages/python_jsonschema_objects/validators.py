import decimal
import logging
import numbers


logger = logging.getLogger(__name__)

SCHEMA_TYPE_MAPPING = (
    ("array", list),
    ("boolean", bool),
    ("integer", int),
    ("number", numbers.Real),
    ("null", type(None)),
    ("string", str),
    ("object", dict),
)
"""Sequence of schema type mappings to be checked in precedence order."""


class ValidationError(Exception):
    pass


class ValidatorRegistry(object):
    def __init__(self):
        self.registry = {}

    def register(self, name=None):
        def f(functor):
            self.registry[name if name is not None else functor.__name__] = functor
            return functor

        return f

    def __call__(self, name):
        return self.registry.get(name)


registry = ValidatorRegistry()


@registry.register()
def multipleOf(param, value, _):
    # This conversion to string is intentional because floats are imprecise.
    # >>> decimal.Decimal(33.069)
    # Decimal('33.0690000000000026147972675971686840057373046875')
    # >>> decimal.Decimal('33.069')
    # Decimal('33.069')
    value = decimal.Decimal(str(value))
    divisor = decimal.Decimal(str(param))
    if value % divisor != 0:
        raise ValidationError("{0} is not a multiple of {1}".format(value, param))


@registry.register()
def enum(param, value, _):
    if value not in param:
        raise ValidationError("{0} is not one of {1}".format(value, param))


@registry.register()
def const(param, value, _):
    if value != param:
        raise ValidationError("{0} is not constant {1}".format(value, param))


@registry.register()
def minimum(param, value, type_data):
    exclusive = type_data.get("exclusiveMinimum")
    if exclusive:
        if value <= param:
            raise ValidationError(
                "{0} is less than or equal to {1}".format(value, param)
            )
    elif value < param:
        raise ValidationError("{0} is less than {1}".format(value, param))


@registry.register()
def maximum(param, value, type_data):
    exclusive = type_data.get("exclusiveMaximum")
    if exclusive:
        if value >= param:
            raise ValidationError(
                "{0} is greater than or equal to {1}".format(value, param)
            )
    elif value > param:
        raise ValidationError("{0} is greater than {1}".format(value, param))


@registry.register()
def maxLength(param, value, _):
    if len(value) > param:
        raise ValidationError("{0} is longer than {1} characters".format(value, param))


@registry.register()
def minLength(param, value, _):
    if len(value) < param:
        raise ValidationError("{0} is fewer than {1} characters".format(value, param))


@registry.register()
def pattern(param, value, _):
    import re

    match = re.search(param, value)
    if not match:
        raise ValidationError("{0} does not match {1}".format(value, param))


try:
    from jsonschema import FormatChecker
except ImportError:
    pass
else:

    @registry.register()
    def format(param, value, _):
        if not FormatChecker().conforms(value, param):
            raise ValidationError(
                "'{0}' is not formatted as a {1}".format(value, param)
            )


type_registry = ValidatorRegistry()


@type_registry.register(name="boolean")
def check_boolean_type(param, value, _):
    if not isinstance(value, bool):
        raise ValidationError("{0} is not a boolean".format(value))


@type_registry.register(name="integer")
def check_integer_type(param, value, _):
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValidationError("{0} is not an integer".format(value))


@type_registry.register(name="number")
def check_number_type(param, value, _):
    if not isinstance(value, numbers.Real):
        raise ValidationError("{0} is neither an integer nor a float".format(value))


@type_registry.register(name="null")
def check_null_type(param, value, _):
    if value is not None:
        raise ValidationError("{0} is not None".format(value))


@type_registry.register(name="string")
def check_string_type(param, value, _):
    if not isinstance(value, str):
        raise ValidationError("{0} is not a string".format(value))


@type_registry.register(name="array")
def check_array_type(param, value, _):
    if not isinstance(value, list):
        raise ValidationError("{0} is not an array".format(value))


@type_registry.register(name="object")
def check_object_type(param, value, _):
    from python_jsonschema_objects.classbuilder import ProtocolBase

    if not isinstance(value, (dict, ProtocolBase)):
        raise ValidationError(
            "{0} is not an object (neither dict nor ProtocolBase)".format(value)
        )


@registry.register(name="type")
def check_type(param, value, type_data):
    type_check = type_registry(param)
    if type_check is None:
        raise ValidationError("{0} is an invalid type".format(value))
    type_check(param, value, type_data)
