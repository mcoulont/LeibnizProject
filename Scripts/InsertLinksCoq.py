#!/usr/bin/python3

import sys


SUFFIXE_MARKDOWN = ".md"

TOKEN_LINK_INDEX = "--link_index--"
TOKEN_LINKS_COQ = "--links_coq--"
TOKEN_ARTICLE = "$article$"

file_template_link_index = sys.argv[1]
file_template_links_coq = sys.argv[2]
basename_without_extension = sys.argv[3]
html_article = sys.stdin.read()

template_links_coq = open(file_template_links_coq).read()

template_links_coq = template_links_coq.replace(
	TOKEN_ARTICLE,
	basename_without_extension + ".v"
)

html_article = html_article.replace(
	TOKEN_LINK_INDEX,
	open(file_template_link_index).read()
).replace(
	TOKEN_LINKS_COQ,
	template_links_coq
)

print(html_article)
