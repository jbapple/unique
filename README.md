unique
======

A purely-functional uniquely represented dictionary.
Any two dictionaries representing the same set of elements have the same shape and the same elements in the same positions.
Additionally, any two dictionaries of the same size have the same shape.

As a result of this restriction, the operations on this dictionary are slower than those on dictionaries that are not uniquely represented, such as red-black trees.