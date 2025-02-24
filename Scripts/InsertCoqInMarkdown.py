#!/usr/bin/python3

import sys
from re import finditer


SUFFIXE_MARKDOWN = ".md"
REGEX_COQ_INSERTION = "\\[//\\]: # \\((\\d+)-(\\d+)\\)"
# TOKEN_MATH_START = "<math>"
# TOKEN_MATH_END = "</math>"
TOKEN_MATH_START = "--MATH_START--"
TOKEN_MATH_END = "--MATH_END--"
START_MATH_BLOCK = "<div class='math_block'>"
END_MATH_BLOCK = "</div>"

folder_coq = sys.argv[1]
file_article_md = sys.argv[2]

if not file_article_md.endswith(SUFFIXE_MARKDOWN):
	print(file_article_md + " should be a Markdown file")
	exit(1)

basename = file_article_md.split('/')[-1][:-len(SUFFIXE_MARKDOWN)]

coq_lines = open(folder_coq + "/" + basename + ".v").readlines()

# We also insert HTML tags to manage the math blocks
article_md = open(file_article_md).read().replace(
	TOKEN_MATH_START,
	START_MATH_BLOCK
).replace(
	TOKEN_MATH_END,
	END_MATH_BLOCK
)

for coq_occurrence in finditer(REGEX_COQ_INSERTION, article_md):
	article_md = article_md.replace(
		coq_occurrence.group(0),
		'```\n' +
		''.join(coq_lines[
            int(coq_occurrence.group(1)) - 1 : int(coq_occurrence.group(2))
        ]) + "\n```"
	)

print(article_md)
