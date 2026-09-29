; A clause is a function's case; its body runs to the lines after it, which
; the grammar keeps flat, so `inside` is its first line's statement.
(clause
  body: (_) @function.inside) @function.around

(signature
  (methods) @class.inside) @class.around

(arguments
  ((_) @parameter.inside . ","? @parameter.around) @parameter.around)

(lambda_parameters
  ((_) @parameter.inside . ","? @parameter.around) @parameter.around)

(lambda
  body: (_) @function.inside) @function.around

(comment) @comment.inside

(comment)+ @comment.around

(expect) @test.around
