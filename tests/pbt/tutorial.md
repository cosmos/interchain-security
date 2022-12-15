# Property Based Testing 

Property based testing works by generating randomish inputs or sequences of inputs which you feed to any code that you want to test.
You defined properties that your code has to satisfy e.g. 'result is sorted' or 'result is positive' and the PBT library will try
to generate sequences to make your code violate the properties. If it does, the PBT library will minimize the complexity of the input
to the smallest size possible, to make debugging your code easier.

This is the basic idea but there are many places where it is explained better, I recommend just googling for blog posts about it. In
particular I can recommend this page which contains links to solid tutorials https://jqwik.net/property-based-testing.html and this
tutorial in particular https://johanneslink.net/how-to-specify-it/

## Resources

1. Rapid golang library - better than alternatives but poorly documented https://github.com/flyingmutant/rapid
2. Jqwik java library - very easy to use and feature rich https://jqwik.net/
3. Jqwik page about property based testing in general - contains a lot of resource links https://jqwik.net/property-based-testing.html
4. Python hypothesis github page - hypothesis is the most popular python PBT library https://github.com/HypothesisWorks/hypothesis
5. C++ Rapidcheck github page - rapidcheck is a solid c++ library https://github.com/emil-e/rapidcheck