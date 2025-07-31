#!/usr/bin/python3

import sys
from os import listdir
from re import finditer


SUFFIXE_MARKDOWN = ".md"
REGEX_ROCQ_INSERTION = "\\[//\\]: # Rocq \\((\\d+)-(\\d+)\\)"
REGEX_LEAN_INSERTION = "\\[//\\]: # Lean4 \\((\\d+)-(\\d+)\\)"
TOKEN_MATH_START = "--MATH_START--"
TOKEN_MATH_END = "--MATH_END--"
TOKEN_ROCQ_CODE = "$rocq_code$"
TOKEN_LEAN_CODE = "$lean_code$"
START_MATH_BLOCK = "<div class='math-block'>"
END_MATH_BLOCK = "</div>"


if __name__ == "__main__":
	file_article_md = sys.argv[1]
	folder_rocq = sys.argv[2]
	folder_lean = sys.argv[3]


	if not file_article_md.endswith(SUFFIXE_MARKDOWN):
		print(file_article_md + " should be a Markdown file")
		exit(1)


	# We also insert HTML tags to manage the math blocks
	article_md = open(file_article_md).read().replace(
		TOKEN_MATH_START,
		START_MATH_BLOCK
	).replace(
		TOKEN_MATH_END,
		END_MATH_BLOCK
	)


	basename = file_article_md.split('/')[-1][:-len(SUFFIXE_MARKDOWN)]

	if basename + ".v" in listdir(folder_rocq + "/"):
		rocq_lines = open(folder_rocq + "/" + basename + ".v").readlines()

		for rocq_occurrence in finditer(REGEX_ROCQ_INSERTION, article_md):
			article_md = article_md.replace(
				rocq_occurrence.group(0),
				'```\n' + TOKEN_ROCQ_CODE +
				''.join(rocq_lines[
					int(rocq_occurrence.group(1)) - 1 :
					int(rocq_occurrence.group(2))
				]) + "\n```\n"
			)

	if basename + ".lean" in listdir(folder_lean + "/"):
		lean_lines = open(folder_lean + "/" + basename + ".lean").readlines()

		for lean_occurrence in finditer(REGEX_LEAN_INSERTION, article_md):
			article_md = article_md.replace(
				lean_occurrence.group(0),
				'```\n' + TOKEN_LEAN_CODE +
				''.join(lean_lines[
					int(lean_occurrence.group(1)) - 1 :
					int(lean_occurrence.group(2))
				]) + "\n```\n"
			)


	print(article_md)
