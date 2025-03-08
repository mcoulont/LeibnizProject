#!/bin/bash

folder_current_script=$( cd "$(dirname "${BASH_SOURCE[0]}")" ; pwd -P )

root_folder=$folder_current_script/../
folder_markdown=$folder_current_script/../Markdown
folder_html=$folder_current_script/../Articles
folder_coq=$folder_current_script/../Coq/Articles

file_general_template=$folder_current_script/../Templates/general.html
file_template_link_index=$folder_current_script/../Templates/link_index.html
file_template_links_coq=$folder_current_script/../Templates/links_coq.html
file_coq_project=$folder_current_script/../Coq/_CoqProject
index_file=$folder_current_script/../index.html

script_insert_coq=$folder_current_script/InsertCoqInMarkdown.py
script_insert_links_coq=$folder_current_script/InsertLinksCoq.py
script_generate_index=$folder_current_script/GenerateIndex.py

mkdir -p $folder_html

for file_article_md in $folder_markdown/*; do
    base_name=$(basename $file_article_md)
    basename_without_extension="${base_name%.*}"

    python3 $script_insert_coq $folder_coq $file_article_md | \
    pandoc -f markdown --mathjax --template=$file_general_template | \
    python3 $script_insert_links_coq $file_template_link_index $file_template_links_coq $basename_without_extension > $folder_html/$basename_without_extension.html
done

python3 $script_generate_index $file_general_template $folder_markdown $file_coq_project > $root_folder/index.html
