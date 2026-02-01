import inspect
import os
import re
import sys
import textwrap
from collections import namedtuple

from sphinx.application import Sphinx
from sphinx.builders._epub_base import EpubBuilder
from sphinx.builders.dirhtml import DirectoryHTMLBuilder
from sphinx.builders.singlehtml import SingleFileHTMLBuilder
from sphinx.errors import ExtensionError

from .theme_check import only_pallets_theme
from .theme_check import set_is_pallets_theme
from .versions import load_versions

try:
    from importlib import metadata as importlib_metadata
except ImportError:
    # Python <3.8 compatibility
    import importlib_metadata


def setup(app):
    base = os.path.join(os.path.dirname(__file__), "themes")

    for name in os.listdir(base):
        path = os.path.join(base, name)

        if os.path.isdir(path):
            app.add_html_theme(name, path)

    app.add_config_value("is_pallets_theme", None, "html")

    app.connect("builder-inited", set_is_pallets_theme)
    app.connect("builder-inited", load_versions)
    app.connect("html-collect-pages", add_404_page)
    app.connect("html-page-context", canonical_url)

    try:
        app.connect("autodoc-skip-member", skip_internal)
        app.connect("autodoc-process-docstring", cut_module_meta)
    except ExtensionError:
        pass

    try:
        app.add_config_value("singlehtml_sidebars", None, "html")
    except ExtensionError:
        pass
    else:
        app.connect("builder-inited", singlehtml_sidebars)

    from .themes import click as click_ext
    from .themes import jinja as jinja_ext

    click_ext.setup(app)
    jinja_ext.setup(app)

    own_release, _ = get_version(__name__)
    return {"version": own_release, "parallel_read_safe": True}


@only_pallets_theme(default=())
def add_404_page(app):
    """Build an extra ``404.html`` page if no ``"404"`` key is in the
    ``html_additional_pages`` config.
    """
    is_epub = isinstance(app.builder, EpubBuilder)
    config_pages = app.config.html_additional_pages

    if not is_epub and "404" not in config_pages:
        yield ("404", {}, "404.html")


@only_pallets_theme()
def canonical_url(app: Sphinx, pagename, templatename, context, doctree):
    """Sphinx 1.8 builds a canonical URL if ``html_baseurl`` config is
    set. However, it builds a URL ending with ".html" when using the
    dirhtml builder, which is incorrect. Detect this and generate the
    correct URL for each page.

    Also accepts the custom, deprecated ``canonical_url`` config as the
    base URL. This will be removed in version 2.1.
    """
    base = app.config.html_baseurl

    if not base and context.get("canonical_url"):
        import warnings

        warnings.warn(
            "'canonical_url' config is deprecated and will be removed"
            " in Pallets-Sphinx-Themes 2.1. Set Sphinx's 'html_baseurl'"
            " config instead.",
            DeprecationWarning,
        )
        base = context["canonical_url"]

    if (
        not base
        or not isinstance(app.builder, DirectoryHTMLBuilder)
        or not context["pageurl"]
        or not context["pageurl"].endswith(".html")
    ):
        return

    # Fix pageurl for dirhtml builder if this version of Sphinx still
    # generates .html URLs.
    target = app.builder.get_target_uri(pagename)
    context["pageurl"] = base + target


@only_pallets_theme()
def singlehtml_sidebars(app):
    """When using a ``singlehtml`` builder, replace the
    ``html_sidebars`` config with ``singlehtml_sidebars``. This can be
    used to change what sidebars are rendered for the single page called
    ``"index"`` by the builder.
    """
    if app.config.singlehtml_sidebars is not None and isinstance(
        app.builder, SingleFileHTMLBuilder
    ):
        app.config.html_sidebars = app.config.singlehtml_sidebars


@only_pallets_theme()
def skip_internal(app, what, name, obj, skip, options):
    """Skip rendering autodoc when the docstring contains a line with
    only the string `:internal:`.
    """
    docstring = inspect.getdoc(obj) or ""

    if skip or re.search(r"^\s*:internal:\s*$", docstring, re.M) is not None:
        return True


@only_pallets_theme()
def cut_module_meta(app, what, name, obj, options, lines):
    """Don't render lines that start with ``:copyright:`` or
    ``:license:`` when rendering module autodoc. These lines are useful
    meta information in the source code, but are noisy in the docs.
    """
    if what != "module":
        return

    lines[:] = [
        line for line in lines if not line.startswith((":copyright:", ":license:"))
    ]


def get_version(name, version_length=2, placeholder="x"):
    """Ensures that the named package is installed and returns version
    strings to be used by Sphinx.

    Sphinx uses ``version`` to mean an abbreviated form of the full
    version string, which is called ``release``. In ``conf.py``::

        release, version = get_version("Flask")
        # release = 1.0.x, version = 1.0.3.dev0

    :param name: Name of package to get.
    :param version_length: How many values from ``release`` to use for
        ``version``.
    :param placeholder: Extra suffix to add to the version. The default
        produces versions like ``1.2.x``.
    :return: ``(release, version)`` tuple.
    """
    try:
        release = importlib_metadata.version(name)
    except ImportError:
        print(
            textwrap.fill(
                "'{name}' must be installed to build the documentation."
                " Install from source using `pip install -e .` in a"
                " virtualenv.".format(name=name)
            )
        )
        sys.exit(1)

    version = ".".join(release.split(".", version_length)[:version_length])

    if placeholder:
        version = f"{version}.{placeholder}"

    return release, version


#: ``(title, url)`` named tuple that will be rendered with
ProjectLink = namedtuple("ProjectLink", ("title", "url"))
