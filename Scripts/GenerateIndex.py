#!/usr/bin/python3

import sys
from re import finditer, search, sub


TOKEN_LINK_INDEX = "--link_index--"
TOKEN_LINKS_COQ = "--links_coq--"
TOKEN_BODY = "$body$"
INDEX_TITLE = "A website aiming at global formalization"
REGEX_MATHJAX = "\\$if\\(math\\)\\$\\s+\\$math\\$\\s+\\$endif\\$"
REGEX_TITLE_MD = """title\\s*:\\s*['"]([^'"]+)['"]\\s+author\\s*:"""
FOLDER_HTML = "Articles/"
REGEX_BASENAME_COQ_PROJECT = "(?<!#)\\./Articles/([a-z0-9_]+)\\.v\\s"

file_general_template = sys.argv[1]
folder_markdown = sys.argv[2]
file_coq_project = sys.argv[3]

body_html = "<ul>"

# The articles must be in the index in the same order as in _CoqProject
# (to be consistent with imports)
for occurrence_article_basename in finditer(
    REGEX_BASENAME_COQ_PROJECT,
    open(file_coq_project).read()
):
    body_html += (
        '<li><a href="' + FOLDER_HTML + occurrence_article_basename.group(1) +
        '.html">' + search(
            REGEX_TITLE_MD,
            open(folder_markdown + '/' + occurrence_article_basename.group(1) +
            ".md").read()
        ).group(1) + '</a></li>'
    )

body_html += "</ul>"

print(
    sub(
        REGEX_MATHJAX,
        "",
        open(file_general_template).read().replace(
            "$title$",
            INDEX_TITLE
        ).replace(
            TOKEN_LINK_INDEX,
            ""
        ).replace(
            TOKEN_LINKS_COQ,
            ""
        ).replace(
            TOKEN_BODY,
            body_html
        ).replace(
            "../",
            ""
        )
    )
)
