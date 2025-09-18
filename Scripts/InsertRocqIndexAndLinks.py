#!/usr/bin/python3

import sys
from os import listdir
from bs4 import BeautifulSoup
from re import findall, sub
from time import time


class LinkToRocqObject:
	def __init__(
		self,
		object_type: str,
		url: str,
		is_relative: bool
	):
		self.__object_type = object_type
		self.__url = url
		self.__is_relative = is_relative

	def get_object_type(self) -> str:
		return self.__object_type

	def get_url(self) -> str:
		return self.__url

	def is_relative(self) -> bool:
		return self.__is_relative


if __name__ == "__main__":
	start = time()

	folder_html = sys.argv[1]
	folder_rocq_articles = sys.argv[2]
	folder_rocq_tools = sys.argv[3]
	file_homepage = sys.argv[4]


	TOKEN_ROCQ_INDEX = '<div id="rocq-index">'

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


	links_to_rocq_objects: dict[str, LinkToRocqObject] = dict()


	# Detect the Rocq objects to point to

	for rocq_tool_file in listdir(folder_rocq_tools):
		if rocq_tool_file.endswith(".v"):
			line_number = 0

			for line_rocq_tool in open(
				folder_rocq_tools + '/' + rocq_tool_file,
				'r',
				encoding="utf-8"
			).readlines():
				line_number += 1

				for res_search_object in findall(
					REGEX_ROCQ_OBJECT_POINTED_TO,
					line_rocq_tool
				):
					if res_search_object[3] in links_to_rocq_objects:
						print(
							"Error: duplicate name " +
							res_search_object[3] + " in " +
							links_to_rocq_objects[
								res_search_object[3]
							].get_url().split('/')[-1] +
							" and " + rocq_tool_file +
							" (we try to avoid this)\n",
							file=sys.stderr
						)
						exit(1)

					links_to_rocq_objects[
						res_search_object[3]
					] = LinkToRocqObject(
						res_search_object[1],
						"https://github.com/mcoulont/LeibnizProject/tree/master/Rocq/Tools/" +
						rocq_tool_file + "#L" + str(line_number),
						False
					)

	for rocq_article_file in listdir(folder_rocq_articles):
		if rocq_article_file.endswith(".v"):
			for res_search_object in findall(
				REGEX_ROCQ_OBJECT_POINTED_TO,
				open(
					folder_rocq_articles + '/' + rocq_article_file,
					'r',
					encoding="utf-8"
				).read()
			):
				if res_search_object[3] in links_to_rocq_objects:
					print(
						"Error: duplicate name " +
						res_search_object[3] + " in " +
						links_to_rocq_objects[
							res_search_object[3]
						].get_url().split('/')[-1] +
						" and " + rocq_article_file +
						" (we try to avoid this)\n",
						file=sys.stderr
					)
					exit(1)

				links_to_rocq_objects[
					res_search_object[3]
				] = LinkToRocqObject(
					res_search_object[1],
					rocq_article_file.split('.')[0] + ".html#" +
					res_search_object[3],
					True
				)


	# Insert links in articles

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

				for object_to_point in links_to_rocq_objects:
					html_rocq_code_block = sub(
						"([^\\w'>/\"])(" + object_to_point + ")([^\\w'/])",
						'\\g<1><a href="' +
						links_to_rocq_objects[object_to_point].get_url() +
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


	# Generating the Rocq index

	html_rocq_index = ""

	for rocq_object in sorted(links_to_rocq_objects.keys()):
		if links_to_rocq_objects[rocq_object].is_relative():
			url_prefix = "Articles/"
		else:
			url_prefix = ""

		html_rocq_index += (
			'<div class="index-item"><a href="' + url_prefix +
			links_to_rocq_objects[rocq_object].get_url() +
			'">' + rocq_object + '</a> (' +
			links_to_rocq_objects[rocq_object].get_object_type().lower() +
			')</div>'
		)

	with open(file_homepage, 'r', encoding="utf-8") as file:
		html_homepage = file.read()

	with open(file_homepage, 'w') as file:
		file.write(
			html_homepage.replace(
				TOKEN_ROCQ_INDEX,
				TOKEN_ROCQ_INDEX + html_rocq_index
			)
		)


	end = time()
	print("InsertCrossArticleLinks took " + str(end - start) + " seconds")
