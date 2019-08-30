// Whether the sequence from s[i] to s[j] inclusive is a palindrome
fn sequence_is_palindrome(s: Vec<char>, i:usize, j: usize) -> bool {
    if i >= j {
        return true;
    }
    if s[i] != s[j] {
        return false;
    }
    return sequence_is_palindrome(s, i + 1, j - 1)
}

fn is_palindrome(s: &str) -> bool {
    return sequence_is_palindrome(s.chars().collect(), 0, s.len() - 1);
}

fn test(s: String, answer: bool) {
    // TODO
}

fn main() {
    let s = "footatoof";
    println!("answer = {}", sequence_is_palindrome(s.chars().collect(), 0, 8));
}
