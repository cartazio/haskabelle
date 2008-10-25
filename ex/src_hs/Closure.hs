module Closure
where


func x y = sum x + addToX y
    where addToX y = x + y 
          addToY x = x + y
          w = addToY x
          sum x = w + x
