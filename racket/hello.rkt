#lang racket

(require racket/control)

(reset
  (+ 1
     (shift k
       (+ (k 5) (k 10)))
     3))
