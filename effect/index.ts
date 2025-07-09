import { Effect, Console } from "effect";

// Fetch a URL in an Effect way
const fetchUrl = (url: string) =>
  Effect.tryPromise({
    try: () => fetch(url).then(res => res.text()),
    catch: (error) => new Error(`Failed to fetch: ${error}`)
  });

function countBytes(html) {
  return new TextEncoder().encode(html).length;
}

// Example program that fetches example.com and counts bytes
const program = Effect.gen(function* () {
  yield* Console.log("Fetching example.com...");
  const html = yield* fetchUrl("https://example.com");
  const bytes = new TextEncoder().encode(html).length;
  yield* Console.log(`example.com is ${bytes} bytes`);
});

Effect.runPromise(program);
