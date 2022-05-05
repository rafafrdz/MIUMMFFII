-module(calculateGeometry).
-compile(nowarn_export_all).
-compile(export_all).
calculateArea() ->
    receive
      {rectangle, W, H} ->
        W * H;
      {circle, R} ->
        3.14 * R * R;
      _ ->
        io:format("We can only calculate area of rectangles or circles.")
    end.