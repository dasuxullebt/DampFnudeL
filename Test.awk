BEGIN {
    matched = 0
}
/^import.*/ {
    if (matched == 0) {
	print $0
	print "import qualified Data.Maybe"
	print "import qualified Data.List"
	print "import qualified Data.Char"
	print "import qualified Extraction"
        matched = 1
        next
    }
}
{ print }
