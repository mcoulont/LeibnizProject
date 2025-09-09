#!/usr/bin/python3

import sys
from os import listdir
from bs4 import BeautifulSoup
from re import findall, sub
from time import time


class ToolLine:
	def __init__(self, tool: str, line: int):
		self._tool = tool
		self._line = line

	def __repr__(self):
		return self._tool + "#L" + str(self._line)

	# def get_tool(self):
	# 	return self._tool

	# def get_line(self):
	# 	return self._line


if __name__ == "__main__":
	start = time()

	folder_html = sys.argv[1]
	folder_rocq_tools = sys.argv[2]

	# We wrap Rocq identifiers in a tag and then create hyperlinks
	# to point to them

	# In Rocq, objects we will point to are "Definition", "Axiom", "Example",
	# "Theorem", "Lemma", "Fact", "Remark", "Corollary", "Proposition", "Property",
	# "Record", "Structure", "Fixpoint", "Inductive"
	# (see https://rocq-prover.org/doc/V8.20.1/refman/language/core/definitions.html,
	# https://rocq-prover.org/doc/V8.20.1/refman/language/core/records.html and
	# https://rocq-prover.org/doc/V8.20.1/refman/language/core/inductive.html)

	ROCQ_ALPHABET_FIRST_LETTER = "[^\\W\\d]"
	ROCQ_ALPHABET_SUBSEQUENT_LETTER = "[\\w']"
	ROCQ_REGEX_IDENTIFIER = (
		ROCQ_ALPHABET_FIRST_LETTER + "(" +
		ROCQ_ALPHABET_SUBSEQUENT_LETTER + ")*"
	)
	# (see https://rocq-prover.org/doc/V8.20.1/refman/language/core/basic.html#grammar-token-unicode_letter)

	REGEX_ROCQ_OBJECT_POINTED_TO = (
		'(^|\\s|>)' +
		"(Definition|Axiom|Example|Theorem|Lemma|Fact|Remark|Corollary|" +
		"Proposition|Property|Record|Structure|Fixpoint|Inductive)" +
		"(\\s+)(" + ROCQ_REGEX_IDENTIFIER + ")([\\s:\\(])"
	)
	rocq_object_to_article: dict[str, str] = dict()
	rocq_object_to_tool: dict[str, ToolLine] = dict()

	# Detecting the rocq objects to point to in articles
	for html_article in listdir(folder_html):
		soup = BeautifulSoup(
			open(folder_html + '/' + html_article, encoding="utf-8").read(),
			'html.parser'
		)

		rocq_blocks = soup.find_all("pre", class_="rocq-code")

		for rocq_block in rocq_blocks:
			rocq_code_blocks = rocq_block.find_all("code")

			for rocq_code_block in rocq_code_blocks:
				for res_search_object in findall(
					REGEX_ROCQ_OBJECT_POINTED_TO,
					str(rocq_code_block)
				):
					if res_search_object[3] in rocq_object_to_article:
						print(
							"Error: duplicate name " +
							res_search_object[3] + " in " +
							rocq_object_to_article[res_search_object[3]] +
							" and " + html_article +
							" (we try to avoid this)\n",
							file=sys.stderr
						)
						exit(1)

					rocq_object_to_article[
						res_search_object[3]
					] = html_article

	# Detecting the rocq objects to point to in the Tools folder
	for rocq_tool in listdir(folder_rocq_tools):
		if rocq_tool.endswith(".v"):
			file_rocq_tool = open(
				folder_rocq_tools + '/' + rocq_tool,
				'r',
				encoding="utf-8"
			)

			line_number = 0

			for line_rocq_tool in file_rocq_tool.readlines():
				line_number += 1

				for res_search_object in findall(
					REGEX_ROCQ_OBJECT_POINTED_TO,
					line_rocq_tool
				):
					if res_search_object[3] in rocq_object_to_tool:
						print(
							"Error: duplicate name " +
							res_search_object[3] + " in " +
							str(rocq_object_to_tool[res_search_object[3]]) +
							" and " + str(ToolLine(rocq_tool, line_number)) +
							" (we try to avoid this)\n",
							file=sys.stderr
						)
						exit(1)

					rocq_object_to_tool[
						res_search_object[3]
					] = ToolLine(rocq_tool, line_number)

			file_rocq_tool.close()

	for html_article in listdir(folder_html):
		content_html_article = open(
			folder_html + '/' + html_article,
			encoding="utf-8"
		).read()

		soup = BeautifulSoup(
			content_html_article,
			'html.parser'
		)

		rocq_blocks = soup.find_all("pre", class_="rocq-code")

		for rocq_block in rocq_blocks:
			rocq_code_blocks = rocq_block.find_all("code")

			for rocq_code_block in rocq_code_blocks:
				html_rocq_code_block = sub(
					REGEX_ROCQ_OBJECT_POINTED_TO,
					'\\g<1>\\g<2>\\g<3><span id="\\g<4>">\\g<4></span>\\g<6>',
					str(rocq_code_block)
				)

				for object_to_point in rocq_object_to_article:
					html_rocq_code_block = sub(
						"([^\\w'>/\"])(" + object_to_point + ")([^\\w'/])",
						'\\g<1><a href="https://leibnizproject.com/Articles/' +
						rocq_object_to_article[object_to_point] +
						'#\\g<2>">\\g<2></a>\\g<3>',
						html_rocq_code_block
					)

				for object_to_point in rocq_object_to_tool:
					html_rocq_code_block = sub(
						"([^\\w'>/\"])(" + object_to_point + ")([^\\w'/])",
						'\\g<1><a href="https://github.com/mcoulont/LeibnizProject/tree/master/Rocq/Tools/' +
						str(rocq_object_to_tool[object_to_point]) +
						'">\\g<2></a>\\g<3>',
						html_rocq_code_block
					)

				content_html_article = content_html_article.replace(
					# The quotes are denoted "&#39;" in the resulting HTML
					# (probably due to the code styling)
					# BeautifulSoup seems to convert back to quotes when it parses
					str(rocq_code_block).replace("'", "&#39;"),
					html_rocq_code_block.replace("'", "&#39;")
				)

		with open(
			folder_html + '/' + html_article,
			"w",
			encoding="utf-8"
		) as f:
  			f.write(content_html_article)

	end = time()
	print("InsertCrossArticleLinks took " + str(end - start) + " seconds")
