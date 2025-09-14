#!/usr/bin/python3

import sys

from InsertCodeInMarkdown import TOKEN_ROCQ_CODE, TOKEN_LEAN_CODE


SUFFIXE_MARKDOWN = ".md"

TOKEN_LINK_HOMEPAGE = "--link_homepage--"
TOKEN_LINKS_PROVERS = "--links_provers--"
TOKEN_SWITCH_PROVER = "--switch_prover--"
TOKEN_ARTICLE = "$article$"
TOKEN_CODE_TAGS = "<pre><code>"
TOKEN_HEART = '<div class="heart">'


if __name__ == "__main__":
	basename_without_extension = sys.argv[1]
	file_template_link_homepage = sys.argv[2]
	file_template_links_provers = sys.argv[3]
	file_template_switch_prover = sys.argv[4]
	file_template_switch_visibility_math_code = sys.argv[5]
	file_template_image_rocq = sys.argv[6]
	file_template_image_lean = sys.argv[7]
	html_article = sys.stdin.read()


	# We set the links common to all the articles pages
	# (links to the homepage and to the Github Rocq and Lean pages),
	# the buttons to switch prover and the logos of provers
	template_links_provers = open(file_template_links_provers, encoding="utf-8").read()
	template_switch_prover = open(file_template_switch_prover, encoding="utf-8").read()

	template_links_provers = template_links_provers.replace(
		TOKEN_ARTICLE,
		basename_without_extension
	)

	html_article = html_article.replace(
		TOKEN_LINK_HOMEPAGE,
		open(file_template_link_homepage, encoding="utf-8").read()
	).replace(
		TOKEN_LINKS_PROVERS,
		template_links_provers
	).replace(
		TOKEN_SWITCH_PROVER,
		template_switch_prover
	).replace(
		TOKEN_CODE_TAGS + TOKEN_ROCQ_CODE,
		open(file_template_image_rocq, encoding="utf-8").read()
	).replace(
		TOKEN_CODE_TAGS + TOKEN_LEAN_CODE,
		open(file_template_image_lean, encoding="utf-8").read()
	).replace(
		TOKEN_HEART,
		TOKEN_HEART +
		open(file_template_switch_visibility_math_code, encoding="utf-8").read()
	)


	print(html_article)
