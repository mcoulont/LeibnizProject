#!/usr/bin/python3

import sys
from os import listdir
from bs4 import BeautifulSoup
from re import findall, sub, finditer
from time import time

from GenerateTableContents import TOKEN_ROCQ_INDEX, TOKEN_LEAN_INDEX


REGEX_BASENAME_ROCQ_ARTICLE = "(#\\s*)?\\./Articles/([a-z0-9_]+)\\.v($|\\s)"
REGEX_BASENAME_ROCQ_TOOL = "(#\\s*)?\\./Tools/([a-z0-9_]+)\\.v($|\\s)"
REGEX_BASENAME_LEAN_ARTICLE = "(--\\s*)?import\\s+Articles\\.([a-z0-9_]+)($|\\s)"
REGEX_BASENAME_LEAN_TOOL = "(--\\s*)?import\\s+Tools\\.([a-z0-9_]+)($|\\s)"

# We wrap Rocq and Lean identifiers in a HTML tag and then create hyperlinks
# to point to them

# In Rocq, objects we will point to are "Definition", "Axiom", "Example",
# "Theorem", "Lemma", "Fact", "Remark", "Corollary", "Proposition", "Property",
# "Record", "Structure", "Fixpoint", "Inductive"
# (see https://rocq-prover.org/doc/V8.20.1/refman/language/core/definitions.html,
# https://rocq-prover.org/doc/V8.20.1/refman/language/core/records.html and
# https://rocq-prover.org/doc/V8.20.1/refman/language/core/inductive.html)

PROVER_ALPHABET_FIRST_LETTER = "[^\\W\\d]"
PROVER_ALPHABET_SUBSEQUENT_LETTER = "[\\w']"
PROVER_REGEX_IDENTIFIER = (
	PROVER_ALPHABET_FIRST_LETTER + "(" +
	PROVER_ALPHABET_SUBSEQUENT_LETTER + ")*"
)
# (see https://rocq-prover.org/doc/V8.20.1/refman/language/core/basic.html#grammar-token-unicode_letter)

REGEX_ROCQ_OBJECT_POINTED_TO = (
	'(^|\\s|>)' +
	"(Definition|Axiom|Example|Theorem|Lemma|Fact|Remark|Corollary|" +
	"Proposition|Property|Record|Structure|Fixpoint|Inductive)" +
	"(\\s+)(" + PROVER_REGEX_IDENTIFIER + ")([\\s:\\(])"
)
REGEX_LEAN_OBJECT_POINTED_TO = (
	'(^|\\s|>)' +
	"(def|theorem|lemma|structure)" +
	"(\\s+)(" + PROVER_REGEX_IDENTIFIER + ")([\\s:\\(])"
)

TOKEN_ROCQ_COMMENT_START = "(*"
TOKEN_ROCQ_COMMENT_END = "*)"
TOKEN_LEAN_COMMENT_START = "/-"
TOKEN_LEAN_COMMENT_END = "-/"
TOKEN_LEAN_COMMENT_LINE = "--"


class LinkToProverObject:
	def __init__(
		self,
		object_type: str,
		url: str,
		is_relative: bool
	):
		self.__object_type = object_type
		self.__url = url
		self.__is_relative = is_relative

	def get_object_type_for_index(self) -> str:
		res = self.__object_type.lower()

		if "def" == res:
			return "definition"
		else:
			return res

	def get_url(self) -> str:
		return self.__url

	def is_relative(self) -> bool:
		return self.__is_relative


def detect_objects_to_point_to(
	for_rocq: bool,
	folder_prover_files: str,
	prover_files: list[str],
	links_to_prover_objects: dict[str, LinkToProverObject],
	for_tools: bool
):
	for prover_file in prover_files:
		line_number = 0
		depth_outcomment = 0

		for line_prover_file in open(
			folder_prover_files + '/' + prover_file +
			(".v" if for_rocq else ".lean"),
			'r',
			encoding="utf-8"
		).readlines():
			line_number += 1

			if 1 < line_prover_file.count(
				TOKEN_ROCQ_COMMENT_START if for_rocq else TOKEN_LEAN_COMMENT_START
			):
				print(
					"Error: multiple comment starts in " +
					prover_file + (".v" if for_rocq else ".lean") +
					" line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			if 1 < line_prover_file.count(
				TOKEN_ROCQ_COMMENT_END if for_rocq else TOKEN_LEAN_COMMENT_END
			):
				print(
					"Error: multiple comment ends in " +
					prover_file + (".v" if for_rocq else ".lean") +
					" line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			if (
				not for_rocq and
				1 < line_prover_file.count(TOKEN_LEAN_COMMENT_LINE)
			):
				print(
					"Error: multiple comment line token in .lean line " +
					str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			not_outcommented_piece = ""

			pos_comment_start = line_prover_file.find(
				TOKEN_ROCQ_COMMENT_START if for_rocq else TOKEN_LEAN_COMMENT_START
			)
			pos_comment_end = line_prover_file.find(
				TOKEN_ROCQ_COMMENT_END if for_rocq else TOKEN_LEAN_COMMENT_END
			)
			pos_comment_line = -1 if for_rocq else line_prover_file.find(
				TOKEN_LEAN_COMMENT_LINE
			)

			if -1 != pos_comment_line:
				depth_outcomment += 1

			if -1 == pos_comment_start and -1 == pos_comment_end:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_prover_file

			elif -1 == pos_comment_end:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_prover_file[0:pos_comment_start]

				depth_outcomment += 1

			elif -1 == pos_comment_start:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_prover_file[
						pos_comment_end + len(
							TOKEN_ROCQ_COMMENT_END if for_rocq
							else TOKEN_LEAN_COMMENT_END
						):
					]

				depth_outcomment -= 1

			elif pos_comment_start < pos_comment_end:
				if 0 == depth_outcomment:
					not_outcommented_piece = (
						line_prover_file[0:pos_comment_start] +
						line_prover_file[
							pos_comment_end + len(
								TOKEN_ROCQ_COMMENT_END if for_rocq
								else TOKEN_LEAN_COMMENT_END
							):
						]
					)

			elif pos_comment_end < pos_comment_start:
				if 0 == depth_outcomment:
					not_outcommented_piece = line_prover_file[
						pos_comment_end + len(
							TOKEN_ROCQ_COMMENT_END if for_rocq
							else TOKEN_LEAN_COMMENT_END
						):
						pos_comment_start
					]

			else:
				print(
					"Error: internal error while parsing comments in " +
					prover_file + (".v" if for_rocq else ".lean") +
					" line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			if depth_outcomment < 0:
				print(
					"Error: unmatched comment end in " +
					prover_file + (".v" if for_rocq else ".lean") +
					" line " + str(line_number) + "\n",
					file=sys.stderr
				)
				exit(1)

			for res_search_object in findall(
				REGEX_ROCQ_OBJECT_POINTED_TO if for_rocq
				else REGEX_LEAN_OBJECT_POINTED_TO,
				not_outcommented_piece
			):
				if res_search_object[3] in links_to_prover_objects:
					print(
						"Error: duplicate name " +
						res_search_object[3] + " in " +
						links_to_prover_objects[
							res_search_object[3]
						].get_url().split('/')[-1] +
						" and " + prover_file +
						(".v" if for_rocq else ".lean") +
						" (we try to avoid this)\n",
						file=sys.stderr
					)
					exit(1)

				if for_tools:
					links_to_prover_objects[
						res_search_object[3]
					] = LinkToProverObject(
						res_search_object[1],
						"https://github.com/mcoulont/LeibnizProject/tree/master/" +
						("Rocq/Tools/" + prover_file +".v#L") if for_rocq
						else ("Lean4/Tools/" + prover_file + ".lean#L") +
						str(line_number),
						False
					)
				else:
					links_to_prover_objects[
						res_search_object[3]
					] = LinkToProverObject(
						res_search_object[1],
						prover_file + ".html#" +
						res_search_object[3],
						True
					)


def insert_indexes_and_links(
	for_rocq: bool,
	folder_html: str,
	folder_prover_articles: str,
	folder_prover_tools: str,
	file_prover_project: str,
	file_homepage: str
) -> None:
	links_to_prover_objects: dict[str, LinkToProverObject] = dict()

	comment_str = "#" if for_rocq else "--"

	# List the prover's files corresponding with articles

	prover_files_articles = []

	for occurrence_article_basename in finditer(
        REGEX_BASENAME_ROCQ_ARTICLE if for_rocq else REGEX_BASENAME_LEAN_ARTICLE,
        open(file_prover_project, encoding="utf-8").read()
    ):
		if not occurrence_article_basename.group(0).startswith(comment_str):
			prover_files_articles.append(occurrence_article_basename.group(2))

	prover_files_tools = []

	for occurrence_article_basename in finditer(
        REGEX_BASENAME_ROCQ_TOOL if for_rocq else REGEX_BASENAME_LEAN_TOOL,
        open(file_prover_project, encoding="utf-8").read()
    ):
		if not occurrence_article_basename.group(0).startswith(comment_str):
			prover_files_tools.append(occurrence_article_basename.group(2))

	# Detect the prover's objects to point to

	detect_objects_to_point_to(
		for_rocq,
		folder_prover_tools,
		prover_files_tools,
		links_to_prover_objects,
		True
	)

	detect_objects_to_point_to(
		for_rocq,
		folder_prover_articles,
		prover_files_articles,
		links_to_prover_objects,
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

		prover_blocks = soup.find_all(
			"pre",
			class_="rocq-code" if for_rocq else "lean-code"
		)

		for prover_block in prover_blocks:
			prover_code_blocks = prover_block.find_all("code")

			for prover_code_block in prover_code_blocks:
				html_prover_code_block = sub(
					REGEX_ROCQ_OBJECT_POINTED_TO if for_rocq
					else REGEX_LEAN_OBJECT_POINTED_TO,
					'\\g<1>\\g<2>\\g<3><span id="\\g<4>">\\g<4></span>\\g<6>',
					str(prover_code_block)
				)

				for object_to_point in links_to_prover_objects:
					html_prover_code_block = sub(
						"([^\\w'>/\"])(" + object_to_point + ")([^\\w'/])",
						'\\g<1><a href="' +
						links_to_prover_objects[object_to_point].get_url() +
						'">\\g<2></a>\\g<3>',
						html_prover_code_block
					)

				content_html_article = content_html_article.replace(
					# The quotes are denoted "&#39;" in the resulting HTML
					# (probably due to the code styling)
					# BeautifulSoup seems to convert back to quotes when it parses
					str(prover_code_block).replace("'", "&#39;"),
					html_prover_code_block.replace("'", "&#39;")
				)

		with open(
			folder_html + '/' + html_article,
			"w",
			encoding="utf-8"
		) as f:
			f.write(content_html_article)

	# Generating the prover's index

	html_prover_index = ""

	for prover_object in sorted(
		links_to_prover_objects.keys(),
		# without the line below, all upper cases are rendered before
		# all lower cases (for instance "TotalOrder" is rendered before "add1_lt")
		key=lambda s: s.lower()
	):
		if links_to_prover_objects[prover_object].is_relative():
			url_prefix = "Articles/"
		else:
			url_prefix = ""

		html_prover_index += (
			'<div class="index-item"><a href="' + url_prefix +
			links_to_prover_objects[prover_object].get_url() +
			'">' + prover_object + '</a> (' +
			links_to_prover_objects[prover_object].get_object_type_for_index() +
			')</div>'
		)

	with open(file_homepage, 'r', encoding="utf-8") as file:
		html_homepage = file.read()

	with open(file_homepage, 'w') as file:
		token_index = TOKEN_ROCQ_INDEX if for_rocq else TOKEN_LEAN_INDEX

		file.write(
			html_homepage.replace(
				token_index,
				token_index + html_prover_index
			)
		)


if __name__ == "__main__":
	start = time()

	folder_html = sys.argv[1]
	folder_rocq_articles = sys.argv[2]
	folder_rocq_tools = sys.argv[3]
	file_rocq_project = sys.argv[4]
	folder_lean_articles = sys.argv[5]
	folder_lean_tools = sys.argv[6]
	file_lean_project = sys.argv[7]
	file_homepage = sys.argv[8]

	insert_indexes_and_links(
		True,
		folder_html,
		folder_rocq_articles,
		folder_rocq_tools,
		file_rocq_project,
		file_homepage
	)

	insert_indexes_and_links(
		False,
		folder_html,
		folder_lean_articles,
		folder_lean_tools,
		file_lean_project,
		file_homepage
	)

	end = time()
	print("InsertCrossArticleLinks took " + str(end - start) + " seconds")
