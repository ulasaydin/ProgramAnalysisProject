# ProgramAnalysisProject
Course project for Group 8 in 02242 Program Analysis at DTU

## Instrumenter

### Declare variables
[From](https://plse.cs.washington.edu/daikon/download/doc/developer/File-formats.html#Variable-declarations)
![yo](imgs/variables_declaration.png)

    var-kind <kind> [<relative-name>]

    Specifies the variable kind. Possible values are: field, function, array, variable, return. If field or function are specified, the relative name of the field or function must be specified. For example, if the variable is this.theArray, the relative name is theArray. Pointers to arrays are of type field. The arrays themselves (a sequence of values) are of type array. A var-kind entry is required in each variable block. 

     dec-type <language-declaration>

    This is what the programmer used in the declaration of the variable. Names for standard types should use Java’s names (e.g., int, boolean, java.lang.String, etc.), but names for user-defined or language-specific types can be arbitrary strings. A dec-type entry is required in each variable block.
