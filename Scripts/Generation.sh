#!/bin/bash

folder_current_script=$( cd "$(dirname "${BASH_SOURCE[0]}")" ; pwd -P )

root_folder=$folder_current_script/../
folder_markdown=$folder_current_script/../Markdown
folder_html=$folder_current_script/../Articles
folder_rocq=$folder_current_script/../Rocq/Articles
folder_lean=$folder_current_script/../Lean4/Articles

file_general_template=$folder_current_script/../Templates/general.html
file_template_link_index=$folder_current_script/../Templates/link_index.html
file_template_links_provers=$folder_current_script/../Templates/links_provers.html
file_template_switch_prover=$folder_current_script/../Templates/switch_prover.html
file_rocq_project=$folder_current_script/../Rocq/_CoqProject
file_lean_project=$folder_current_script/../Lean4/Articles.lean
index_file=$folder_current_script/../index.html

script_insert_code=$folder_current_script/InsertCodeInMarkdown.py
script_insert_links_provers=$folder_current_script/InsertLinksProvers.py
script_generate_index=$folder_current_script/GenerateIndex.py

mkdir -p $folder_html

for file_article_md in $folder_markdown/*; do
    base_name=$(basename $file_article_md)
    basename_without_extension="${base_name%.*}"

    python3 $script_insert_code $file_article_md $folder_rocq $folder_lean | \
    pandoc -f markdown --mathjax --template=$file_general_template | \
    python3 $script_insert_links_provers $file_template_link_index $file_template_links_provers $file_template_switch_prover $basename_without_extension > $folder_html/$basename_without_extension.html
done

python3 $script_generate_index $file_general_template $folder_markdown $file_rocq_project $file_lean_project > $root_folder/index.html
