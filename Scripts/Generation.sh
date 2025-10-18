#!/bin/bash

folder_current_script=$( cd "$(dirname "${BASH_SOURCE[0]}")" ; pwd -P )

root_folder=$folder_current_script/../
folder_markdown=$folder_current_script/../Markdown
folder_html=$folder_current_script/../Articles
folder_rocq_articles=$folder_current_script/../Rocq/Articles
folder_rocq_tools=$folder_current_script/../Rocq/Tools
folder_lean=$folder_current_script/../Lean4/Articles

file_general_template=$folder_current_script/../Templates/general.html
file_template_link_homepage=$folder_current_script/../Templates/link_homepage.html
file_template_links_provers=$folder_current_script/../Templates/links_provers.html
file_template_switch_prover=$folder_current_script/../Templates/switch_prover.html
file_template_switch_visibility_math_code=$folder_current_script/../Templates/switch_visibility_math_code.html
file_template_image_rocq=$folder_current_script/../Templates/image_rocq.html
file_template_image_lean=$folder_current_script/../Templates/image_lean.html
file_rocq_project=$folder_current_script/../Rocq/_CoqProject
file_lean_project=$folder_current_script/../Lean4/Articles.lean
homepage_file=$folder_current_script/../index.html

script_insert_code=$folder_current_script/InsertCodeInMarkdown.py
script_insert_common_html=$folder_current_script/InsertCommonHtml.py
script_generate_table_contents=$folder_current_script/GenerateTableContents.py
script_insert_rocq_index_and_links=$folder_current_script/InsertRocqIndexAndLinks.py

mkdir -p $folder_html
rm -rf $folder_html/*

for file_article_md in $folder_markdown/*; do
    base_name=$(basename $file_article_md)
    basename_without_extension="${base_name%.*}"

    python3 $script_insert_code $file_article_md $folder_rocq_articles $folder_lean | \
    pandoc -f markdown --mathjax --template=$file_general_template | \
    python3 $script_insert_common_html $basename_without_extension $file_template_link_homepage $file_template_links_provers $file_template_switch_prover $file_template_switch_visibility_math_code $file_template_image_rocq $file_template_image_lean > $folder_html/$basename_without_extension.html
done

python3 $script_generate_table_contents $file_general_template $folder_markdown $file_rocq_project $file_lean_project $homepage_file
python3 $script_insert_rocq_index_and_links $folder_html $folder_rocq_articles $folder_rocq_tools $homepage_file
