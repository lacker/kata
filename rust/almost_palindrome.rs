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

fn main() {
    let s = "footatoof";
    println!("answer = {}", sequence_is_palindrome(s.chars().collect(), 0, 8));
}
