from functools import wraps


def set_is_pallets_theme(app):
    """Set the ``is_pallets_theme`` config to ``True`` if the current
    theme is a decedent of the ``pocoo`` theme.
    """
    if app.config.is_pallets_theme is not None:
        return

    theme = getattr(app.builder, "theme", None)

    while theme is not None:
        if theme.name == "pocoo":
            app.config.is_pallets_theme = True
            break

        theme = theme.base
    else:
        app.config.is_pallets_theme = False


def only_pallets_theme(default=None):
    """Create a decorator that calls a function only if the
    ``is_pallets_theme`` config is ``True``.

    Used to prevent Sphinx event callbacks from doing anything if the
    Pallets themes are installed but not used. ::

        @only_pallets_theme()
        def inject_value(app):
            ...

        app.connect("builder-inited", inject_value)

    :param default: Value to return if a Pallets theme is not in use.
    :return: A decorator.
    """

    def decorator(f):
        @wraps(f)
        def wrapped(app, *args, **kwargs):
            if not app.config.is_pallets_theme:
                return default

            return f(app, *args, **kwargs)

        return wrapped

    return decorator
