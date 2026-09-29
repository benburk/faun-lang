; A clause is a function's case, and its body is one expression: a block
; where it has several lines.
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
