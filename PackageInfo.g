#
# MajoranaAlgebras: A package for constructing Majorana algebras and representations.
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#
SetPackageInfo( rec(

PackageName := "MajoranaAlgebras",
Subtitle := "A package for constructing Majorana algebras and representations.",
Version := "1.0",
Date := "16/11/2018", # dd/mm/yyyy format

Persons := [
  rec(
    IsAuthor := true,
    IsMaintainer := true,
    FirstNames := "Markus",
    LastName := "Pfeiffer",
    WWWHome := "https://markusp.morphism.de/",
    Email := "markus.pfeiffer@st-andrews.ac.uk",
    PostalAddress := "School of Computer Science, University of St Andrews, North Haugh, KY16 9SX",
    Place := "St Andrews, UK",
    Institution := "University of St Andrews",
  ),
  rec(
    IsAuthor := true,
    IsMaintainer := true,
    FirstNames := "Madeleine",
    LastName := "Whybrow",
    WWWHome := "https://www.madeleinewhybrow.wordpress.com",
    Email := "mlw10@ic.ac.uk",
    PostalAddress := "Department of Mathematics, Imperial College, South Kensington, SW7 2AZ",
    Place := "London, UK",
    Institution := "Imperial College London",
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := Concatenation( "https://github.com/MWhybrow92/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
#SupportEmail   := "TODO",
PackageWWWHome  := "https://MWhybrow92.github.io/MajoranaAlgebras/",
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "dev",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "MajoranaAlgebras",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A package for constructing Majorana algebras and representations.",
),

Dependencies := rec(
  GAP := ">= 4.8",
  NeededOtherPackages := [ [ "GAPDoc", ">= 1.5" ]
                         , [ "automata", ">= 1.13"]
                         , [ "Gauss", ">=0" ]
                         , [ "AtlasRep", ">=0" ]
                         , [ "datastructures", ">=0.2.2" ] ],
  SuggestedOtherPackages := [ [ "Char0Gauss", ">=0" ] ],
  ExternalConditions := [ ],
),

AvailabilityTest := function()
        return true;
    end,

TestFile := "tst/testall.g",

#Keywords := [ "TODO" ],

));
