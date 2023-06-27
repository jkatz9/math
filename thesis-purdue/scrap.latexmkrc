# Place the files as follows:
# your-project
# ├── main.tex
# ├── .vscode
# │   └── settings.json
# └── .latexmkrc

@default_files = ('main.tex');
$latex              = 'platex %O -synctex=1 -interaction=nonstopmode -file-line-error %S';
$latex_silent       = 'platex -halt-on-error -interaction=batchmode';
$bibtex             = 'pbibtex %O %B';
$biber              = 'biber %O --bblencoding=utf8 -u -U --output_safechars %B';
$dvipdf             = 'dvipdfmx %O -o %D %S -z 0';
$makeindex          = 'upmendex %O -o %D %S';
$out_dir            = './build/out';
$aux_dir            = './build/aux';
$emulate_aux        = 1;
$pdf_mode           = 3;
$pdf_update_method  = 4;
$pdf_update_command = "open -a Skim %S;sleep 0.00001;open -a 'Visual Studio Code'";