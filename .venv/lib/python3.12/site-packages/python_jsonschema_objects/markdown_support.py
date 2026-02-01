import re

import markdown
from markdown.extensions import Extension
from markdown.preprocessors import Preprocessor

try:
    from markdown import __version_info__ as markdown_version_info
except ImportError:
    from markdown import version_info as markdown_version_info


def extract_code_blocks(filename):
    with open(filename) as fin:
        doc = fin.read().split("\n")

    M = markdown.Markdown(extensions=[SpecialFencedCodeExtension()])

    preprocessors = M.preprocessors
    tree_processors = M.treeprocessors

    # Markdown 3.* stores the processors in a class that can be iterated directly.
    # Markdown 2.* stores them in a dict, so we have to pull out the values.
    if markdown_version_info[0] == 2:
        # Note: `markdown.version_info` will be deprecated in favor of
        # `markdown.__version_info__` in later versions of Markdown.
        preprocessors = preprocessors.values()
        tree_processors = tree_processors.values()

    for prep in preprocessors:
        doc = prep.run(doc)

    root = M.parser.parseDocument(doc).getroot()

    for treeproc in tree_processors:
        newRoot = treeproc.run(root)
        if newRoot is not None:
            root = newRoot

    return SpecialFencePreprocessor.EXAMPLES


class SpecialFencedCodeExtension(Extension):
    def extendMarkdown(self, md, md_globals=None):
        """Add FencedBlockPreprocessor to the Markdown instance."""
        md.registerExtension(self)

        if markdown_version_info[0] >= 3:
            md.preprocessors.register(
                SpecialFencePreprocessor(md), "fenced_code_block", 10
            )
        else:
            md.preprocessors.add(
                "fenced_code_block",
                SpecialFencePreprocessor(md),
                ">normalize_whitespace",
            )


class SpecialFencePreprocessor(Preprocessor):
    EXAMPLES = {}
    FENCED_BLOCK_RE = re.compile(
        r"""
(?P<fence>^(?:~{3,}|`{3,}))[ ]*         # Opening ``` or ~~~
(\{?\.?(?P<lang>[a-zA-Z0-9_+-]*))?[ ]*  # Optional {, and lang
# Optional highlight lines, single- or double-quote-delimited
(hl_lines=(?P<quot>"|')(?P<hl_lines>.*?)(?P=quot))?[ ]*
}?[ ]*\n                                # Optional closing }
(?P<code>.*?)(?<=\n)
(?P=fence)[ ]*$""",
        re.MULTILINE | re.DOTALL | re.VERBOSE,
    )

    def __init__(self, md):
        super(SpecialFencePreprocessor, self).__init__(md)

        self.checked_for_codehilite = False
        self.codehilite_conf = {}

    def run(self, lines):
        text = "\n".join(lines)

        while True:
            m = self.FENCED_BLOCK_RE.search(text)
            if m:
                if m.group("lang"):
                    lang = m.group("lang")
                    example = m.group("code")
                    try:
                        self.EXAMPLES[lang].append(example)
                    except KeyError:
                        self.EXAMPLES[lang] = [example]

                text = "%s\n%s" % (text[: m.start()], text[m.end() :])
            else:
                break
        return text.split("\n")


if __name__ == "__main__":
    print(extract_code_blocks())
