#!/usr/bin/python3

import sys
from re import sub, search
from os import listdir


TOKEN_LINK_INDEX = "--link_index--"
TOKEN_LINKS_COQ = "--links_coq--"
TOKEN_BODY = "$body$"
INDEX_TITLE = "A website aiming at global formalization"
REGEX_MATHJAX = "\\$if\\(math\\)\\$\\s+\\$math\\$\\s+\\$endif\\$"
REGEX_TITLE_MD = """title\\s*:\\s*['"]([^'"]+)['"]\\s+author\\s*:"""
FOLDER_HTML = "Articles/"

file_general_template = sys.argv[1]
folder_markdown = sys.argv[2]

body_html = "<ul>"

for article_md in listdir(folder_markdown):
    basename_without_extension = article_md.split('/')[-1].split('.')[0]

    body_html += (
        '<li><a href="' + FOLDER_HTML + basename_without_extension +
        '.html">' + search(
            REGEX_TITLE_MD,
            open(folder_markdown + '/' + article_md).read()
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
