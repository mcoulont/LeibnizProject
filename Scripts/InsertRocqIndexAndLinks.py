#!/usr/bin/python3

import sys
from os import listdir
from bs4 import BeautifulSoup
from re import findall, sub, finditer
from time import time


TOKEN_ROCQ_INDEX = '<div id="rocq-index">'

REGEX_BASENAME_ROCQ_ARTICLE = "(#\\s*)?\\./Articles/([a-z0-9_]+)\\.v($|\\s)"
REGEX_BASENAME_ROCQ_TOOL = "(#\\s*)?\\./Tools/([a-z0-9_]+)\\.v($|\\s)"

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

TOKEN_ROCQ_COMMENT_START = "(*"
TOKEN_ROCQ_COMMENT_END = "*)"


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


def detect_rocq_objects_to_point_to(
	folder_rocq_files: str,
	rocq_files: list[str],
	links_to_rocq_objects: dict[str, LinkToRocqObject],
	for_tools: bool
):
	for rocq_file in rocq_files:
		line_number = 0
		depth_outcomment = 0

		for line_rocq_file in open(
			folder_rocq_files + '/' + rocq_file + ".v",
			'r',
			encoding="utf-8"
		).readlines():
			line_number += 1

			if 1 < line_rocq_file.count(TOKEN_ROCQ_COMMENT_START):
				print(
					"Error: multiple comment starts in " +
					rocq_file + ".v line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			if 1 < line_rocq_file.count(TOKEN_ROCQ_COMMENT_END):
				print(
					"Error: multiple comment ends in " +
					rocq_file + ".v line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			not_outcommented_piece = ""

			pos_comment_start = line_rocq_file.find(TOKEN_ROCQ_COMMENT_START)
			pos_comment_end = line_rocq_file.find(TOKEN_ROCQ_COMMENT_END)

			if -1 == pos_comment_start and -1 == pos_comment_end:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_rocq_file

			elif -1 == pos_comment_end:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_rocq_file[0:pos_comment_start]

				depth_outcomment += 1

			elif -1 == pos_comment_start:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_rocq_file[
						pos_comment_end + len(TOKEN_ROCQ_COMMENT_END):
					]

				depth_outcomment -= 1

			elif pos_comment_start < pos_comment_end:
				if 0 == depth_outcomment:
					not_outcommented_piece = (
						line_rocq_file[0:pos_comment_start] +
						line_rocq_file[
							pos_comment_end + len(TOKEN_ROCQ_COMMENT_END):
						]
					)

			elif pos_comment_end < pos_comment_start:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_rocq_file[
						pos_comment_end + len(TOKEN_ROCQ_COMMENT_END):
						pos_comment_start
					]

			else:
				print(
					"Error: internal error while parsing comments in " +
					rocq_file + ".v line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			if depth_outcomment < 0:
				print(
					"Error: unmatched comment end in " +
					rocq_file + ".v line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			for res_search_object in findall(
				REGEX_ROCQ_OBJECT_POINTED_TO,
				not_outcommented_piece
			):
				if res_search_object[3] in links_to_rocq_objects:
					print(
						"Error: duplicate name " +
						res_search_object[3] + " in " +
						links_to_rocq_objects[
							res_search_object[3]
						].get_url().split('/')[-1] +
						" and " + rocq_file +
						".v (we try to avoid this)\n",
						file=sys.stderr
					)
					exit(1)

				if for_tools:
					links_to_rocq_objects[
						res_search_object[3]
					] = LinkToRocqObject(
						res_search_object[1],
						"https://github.com/mcoulont/LeibnizProject/tree/master/Rocq/Tools/" +
						rocq_file + ".v#L" + str(line_number),
						False
					)
				else:
					links_to_rocq_objects[
						res_search_object[3]
					] = LinkToRocqObject(
						res_search_object[1],
						rocq_file + ".html#" +
						res_search_object[3],
						True
					)


if __name__ == "__main__":
	start = time()

	folder_html = sys.argv[1]
	folder_rocq_articles = sys.argv[2]
	folder_rocq_tools = sys.argv[3]
	file_rocq_project = sys.argv[4]
	file_homepage = sys.argv[5]

	links_to_rocq_objects: dict[str, LinkToRocqObject] = dict()


	# List the active Rocq files

	rocq_articles = []

	for occurrence_article_basename in finditer(
        REGEX_BASENAME_ROCQ_ARTICLE,
        open(file_rocq_project, encoding="utf-8").read()
    ):
		if not occurrence_article_basename.group(0).startswith("#"):
			rocq_articles.append(occurrence_article_basename.group(2))

	rocq_tools = []

	for occurrence_article_basename in finditer(
        REGEX_BASENAME_ROCQ_TOOL,
        open(file_rocq_project, encoding="utf-8").read()
    ):
		if not occurrence_article_basename.group(0).startswith("#"):
			rocq_tools.append(occurrence_article_basename.group(2))


	# Detect the Rocq objects to point to

	detect_rocq_objects_to_point_to(
		folder_rocq_tools,
		rocq_tools,
		links_to_rocq_objects,
		True
	)

	detect_rocq_objects_to_point_to(
		folder_rocq_articles,
		rocq_articles,
		links_to_rocq_objects,
		False
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

	for rocq_object in sorted(
		links_to_rocq_objects.keys(),
		# without the line below, all upper cases are rendered before
		# all lower cases (for instance "TotalOrder" is rendered before "add1_lt")
		key=lambda s: s.lower()
	):
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
