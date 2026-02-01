import imp


def import_numpy():
    """
    Returns the numpy module if it exists on the system,
    otherwise returns None.
    """
    try:
        imp.find_module('numpy')
        numpy_exists = True
    except ImportError:
        numpy_exists = False

    if numpy_exists:
        # We do this outside of try/except block in case numpy exists
        # but is not installed correctly. We do not want to catch an
        # incorrect installation which would manifest as an
        # ImportError.
        import numpy as np
    else:
        np = None

    return np
