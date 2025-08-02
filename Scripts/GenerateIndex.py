#!/usr/bin/python3

import sys
from re import finditer, search, sub

from ManageCommonHtml import (
    TOKEN_LINK_INDEX,
    TOKEN_LINKS_PROVERS,
    TOKEN_SWITCH_PROVER
)


TOKEN_BODY = "$body$"
INDEX_TITLE = "A website aiming at global formalization"
REGEX_MATHJAX = "\\$if\\(math\\)\\$\\s+\\$math\\$\\s+\\$endif\\$"
REGEX_TITLE_MD = """title\\s*:\\s*"([^"]+)"\\s+author\\s*:"""
FOLDER_HTML = "Articles/"
REGEX_BASENAME_ROCQ_PROJECT = "(#\\s*)?\\./Articles/([a-z0-9_]+)\\.v($|\\s)"
REGEX_BASENAME_LEAN_PROJECT = "(--\\s*)?import\\s+Articles\\.([a-z0-9_]+)($|\\s)"

file_general_template = sys.argv[1]
folder_markdown = sys.argv[2]
file_rocq_project = sys.argv[3]
file_lean_project = sys.argv[4]


# To be consistent with imports, the articles must be in the index
# in an order consistent with the ones in _CoqProject and Articles.lean
def order_articles (
    articles_in_rocq: list[str],
    articles_in_lean: list[str]
) -> list[str]:
    if 0 == len(articles_in_lean):
        res = articles_in_rocq
    else:
        lastTermL2 = articles_in_lean[-1]

        if lastTermL2 in articles_in_rocq:
            idxLastTermL2InL1 = articles_in_rocq.index(lastTermL2)

            res = order_articles(
                articles_in_rocq[0:idxLastTermL2InL1],
                articles_in_lean[:-1]
            ) + articles_in_rocq[idxLastTermL2InL1:]
        else:
            res = order_articles(articles_in_rocq, articles_in_lean[:-1]) + [lastTermL2]

    return res

def contains_duplicate(l: list) -> bool:
    return len(l) != len(set(l))


body_html = "<ul>"

articles_in_rocq = []

for occurrence_article_basename in finditer(
    REGEX_BASENAME_ROCQ_PROJECT,
    open(file_rocq_project, encoding="utf-8").read()
):
    if not occurrence_article_basename.group(0).startswith("#"):
        articles_in_rocq.append(occurrence_article_basename.group(2))

articles_in_lean = []

for occurrence_article_basename in finditer(
    REGEX_BASENAME_LEAN_PROJECT,
    open(file_lean_project, encoding="utf-8").read()
):
    if not occurrence_article_basename.group(0).startswith("--"):
        articles_in_lean.append(occurrence_article_basename.group(2))

articles = order_articles(articles_in_rocq, articles_in_lean)

if contains_duplicate(articles):
    print("Error: the list of articles contains duplicate values")
    print(articles)
    exit(1)

for article_basename in articles:
    body_html += (
        '<li><a href="' + FOLDER_HTML + article_basename +
        '.html">' + search(
            REGEX_TITLE_MD,
            open(
                folder_markdown + '/' + article_basename + ".md",
                encoding="utf-8"
            ).read()
        ).group(1) + '</a></li>'
    )

body_html += "</ul>"

print(
    sub(
        REGEX_MATHJAX,
        "",
        open(file_general_template, encoding="utf-8").read().replace(
            "$title$",
            INDEX_TITLE
        ).replace(
            TOKEN_LINK_INDEX,
            ""
        ).replace(
            TOKEN_LINKS_PROVERS,
            ""
        ).replace(
            TOKEN_SWITCH_PROVER,
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
