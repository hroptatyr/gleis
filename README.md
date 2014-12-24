gleis (GLEI snippets)
=====================

A few snippets to work with LEI data provided by [p-lei.org](http://p-lei.org)
and [c-lei.org](http://c-lei.org).

Their XML files are based on the [LEIROC](http://www.leiroc.org) schema
but tend to be too large for xslt processors to be handled.

The snippets in this project employ a [SAX parser][1] to convert them
into various output formats (only [turtle][2] at the moment).

  [1]: http://xmlsoft.org/interface.html
  [2]: http://www.w3.org/TR/turtle/
