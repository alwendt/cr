#!/usr/bin/perl
#
#  Add module names to local labels
#
#: m_id: 0
#  ...
#JZ Label -2
#=>
#: m_id: 0
#  ...
#JZ Label m0l-2

while (<>) {
    if (/^: m_id:/) {
        ($module = $_) =~ s/: m_id: //;
        chop($module);
        $replacement = "Label M$module" . "L";
        print $_;
        }
    else {
        s/Label (.*)/$replacement$1/;
        print $_;
        }
    }


