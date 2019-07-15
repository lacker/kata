const volcano = require("./volcano");

test("basic usage", () => {
  let response = volcano([4, 4, 4, 4]);
  expect(response[0]).toBeCloseTo(0.25, 4);
  expect(response[1]).toBeCloseTo(0.25, 4);
  expect(response[2]).toBeCloseTo(0.25, 4);
  expect(response[3]).toBeCloseTo(0.25, 4);

  response = volcano([1, 2]);
  expect(response[1]).toBeGreaterThan(response[0]);
});
