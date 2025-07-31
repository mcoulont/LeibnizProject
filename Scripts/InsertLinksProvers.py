#!/usr/bin/python3

import sys

from InsertCodeInMarkdown import TOKEN_ROCQ_CODE, TOKEN_LEAN_CODE


SUFFIXE_MARKDOWN = ".md"

TOKEN_LINK_INDEX = "--link_index--"
TOKEN_LINKS_PROVERS = "--links_provers--"
TOKEN_SWITCH_PROVER = "--switch_prover--"
TOKEN_ARTICLE = "$article$"
TOKEN_CODE_TAGS = "<pre><code>"


if __name__ == "__main__":
	file_template_link_index = sys.argv[1]
	file_template_links_provers = sys.argv[2]
	file_template_switch_prover = sys.argv[3]
	basename_without_extension = sys.argv[4]
	html_article = sys.stdin.read()


	template_links_provers = open(file_template_links_provers).read()
	template_switch_prover = open(file_template_switch_prover).read()

	template_links_provers = template_links_provers.replace(
		TOKEN_ARTICLE,
		basename_without_extension
	)

	html_article = html_article.replace(
		TOKEN_LINK_INDEX,
		open(file_template_link_index).read()
	).replace(
		TOKEN_LINKS_PROVERS,
		template_links_provers
	).replace(
		TOKEN_SWITCH_PROVER,
		template_switch_prover
	).replace(
		TOKEN_CODE_TAGS + TOKEN_ROCQ_CODE,
		"""<pre class='code-block rocq-code'>
		<img src='../Images/Rocq_logo.ico' height='20' width='20' title='Rocq code' class='prover-icon'>
		<code>"""
	).replace(
		TOKEN_CODE_TAGS + TOKEN_LEAN_CODE,
		"""<pre class='code-block lean-code'>
		<img src='../Images/Lean_logo.jpg' height='20' width='20' title='Lean4 code' class='prover-icon'>
		<code>"""
	)


	print(html_article)
