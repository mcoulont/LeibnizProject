#!/usr/bin/python3

import sys
from re import finditer, search, sub, DOTALL

from InsertCommonHtml import (
    TOKEN_LINK_HOMEPAGE,
    TOKEN_LINKS_PROVERS,
    TOKEN_SWITCH_PROVER
)


TOKEN_BODY = "$body$"
HOMEPAGE_TITLE = "A website aiming at global formalization"
REGEX_MATHJAX = "\\$if\\(math\\)\\$\\s+\\$math\\$\\s+\\$endif\\$"
REGEX_TITLE_MD = """title\\s*:\\s*"([^"]+)"\\s+author\\s*:"""
FOLDER_HTML = "Articles/"
REGEX_BASENAME_ROCQ_PROJECT = "(#\\s*)?\\./Articles/([a-z0-9_]+)\\.v($|\\s)"
REGEX_BASENAME_LEAN_PROJECT = "(--\\s*)?import\\s+Articles\\.([a-z0-9_]+)($|\\s)"
REGEX_KEYWORDS = "keywords:\\n  - ([a-zA-Z0-9 ]+)\\n(  - ([a-zA-Z0-9 ]+)\\n)?"


class Section:
    def __init__(self,
        name: str,
        article: str,
        subsection: str|None = None
    ):
        self.__name = name

        if None == subsection:
            self.__subsections: dict[str, list[str]] = dict()
            self.__articles: list[str] = [article]
        else:
            self.__subsections: dict[str, list[str]] = {subsection: [article]}
            self.__articles: list[str] = []

    def get_name(self) -> str:
        return self.__name

    def get_articles(self) -> list[str]:
        return self.__articles

    def get_subsections(self) -> dict[str, list[str]]:
        return self.__subsections

    def get_subsection(self, name: str) -> dict[str, list[str]]:
        return self.__subsections[name]

    def get_nbr_articles(self) -> int:
        return len(self.__articles)

    def get_nbr_subsections(self) -> int:
        return len(self.__subsections)

    def add_article(self, article: str) -> None:
        self.__articles.append(article)

    def add_article_in_subsection(self, article: str, subsection: str) -> None:
        if subsection in self.__subsections:
            self.__subsections[subsection].append(article)
        else:
            self.__subsections[subsection] = [article]

class SectionsToArticles:
    def __init__(self):
        self.__sections: list[Section] = []

    def get_sections(self) -> list[Section]:
        return self.__sections

    def get_section(self, name_section: str) -> Section|None:
        for section in self.__sections:
            if section.get_name() == name_section:
                return section

        return None

    def add_section(self,
        article_basename: str,
        section: str,
        subsection: str|None
    ) -> None:
        key_section = self.get_section(section)

        if None == subsection or not subsection[0].isupper():
            if None == key_section:
                self.__sections.append(Section(section, article_basename))
            else:
                key_section.add_article(article_basename)
        else:
            if None == key_section:
                self.__sections.append(Section(section, article_basename, subsection))
            else:
                key_section.add_article_in_subsection(article_basename, subsection)


# To be consistent with imports, the articles must be in the table of contents
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


if __name__ == "__main__":
    file_general_template = sys.argv[1]
    folder_markdown = sys.argv[2]
    file_rocq_project = sys.argv[3]
    file_lean_project = sys.argv[4]
    file_homepage = sys.argv[5]

    body_html = """<div>
        <div class="choose-display">
            <div class="choose-display-item" id="choose-table">Table of contents</div>
            <div class="choose-display-item" id="choose-index">Rocq index</div>
            <!--div class="choose-display-item choose-display-filler"></div-->
        </div>
    </div>"""

    body_html += '<div id="table-contents">'

    body_html += "<ul>"

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
        print(
            "Error: the list of articles contains duplicate values",
            articles,
            '\n',
            file=sys.stderr
        )
        exit(1)

    sections_to_articles = SectionsToArticles()

    for article_basename in articles:
        keywords = search(
            REGEX_KEYWORDS,
            open(
                folder_markdown + '/' + article_basename + ".md",
                encoding="utf-8"
            ).read(),
            flags=DOTALL
        )

        if None == keywords:
            print(
                "Error: Keywords of ",
                article_basename,
                ' not found\n',
                file=sys.stderr
            )
            exit(1)

        sections_to_articles.add_section(
            article_basename,
            keywords.group(1),
            keywords.group(3)
        )

    for section in sections_to_articles.get_sections():
        body_html += '<li class="section">' + section.get_name() + '</li>'

        if 0 < section.get_nbr_articles():
            body_html += "<ul>"

            for article in section.get_articles():
                body_html += (
                    '<li class="table-contents-item"><a href="' +
                    FOLDER_HTML + article + '.html">' +
                    search(
                        REGEX_TITLE_MD,
                        open(
                            folder_markdown + '/' + article + ".md",
                            encoding="utf-8"
                        ).read()
                    ).group(1) + '</a></li>'
                )

            body_html += "</ul>"

        if 0 < section.get_nbr_subsections():
            body_html += "<ul>"

            for subsection in section.get_subsections():
                body_html += '<li class="subsection">' + subsection + '</li>'

                for article in section.get_subsection(subsection):
                    body_html += "<ul>"

                    body_html += (
                        '<li class="table-contents-item"><a href="' +
                        FOLDER_HTML + article + '.html">' +
                        search(
                            REGEX_TITLE_MD,
                            open(
                                folder_markdown + '/' + article + ".md",
                                encoding="utf-8"
                            ).read()
                        ).group(1) + '</a></li>'
                    )

                    body_html += "</ul>"

            body_html += "</ul>"

    body_html += "</ul>"

    body_html += "</div>"

    body_html += '<div id="rocq-index">'

    body_html += "</div>"

    with open(
        file_homepage,
        "w",
        encoding="utf-8"
    ) as f:
        f.write(
            sub(
                REGEX_MATHJAX,
                "",
                open(file_general_template, encoding="utf-8").read().replace(
                    "$title$",
                    HOMEPAGE_TITLE
                ).replace(
                    TOKEN_LINK_HOMEPAGE,
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
