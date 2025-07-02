import { Effect, Console } from "effect";

const program = Console.log("hello effect world!");

Effect.runSync(program);

// Fetch a URL in an Effect way
const fetchUrl = (url: string) =>
  Effect.tryPromise({
    try: () => fetch(url).then(res => res.json()),
    catch: (error) => new Error(`Failed to fetch: ${error}`)
  });
