// Whether the sequence from s[i] to s[j] inclusive is a palindrome
fn is_palindrome(s: &[char]) -> bool {
    if s.len() < 2 {
        return true;
    }
    let last = s.len() - 1;
    if s[0] != s[last] {
        return false;
    }
    is_palindrome(&s[1..last])
}

fn test_palindrome(s: &str) {
    let chars: Vec<char> = s.chars().collect();
    println!("is_palindrome(\"{}\") = {}", s, is_palindrome(&chars));
}

fn main() {
    test_palindrome("");
    test_palindrome("x");
    test_palindrome("oo");
    test_palindrome("boof");
    test_palindrome("pogop");
    test_palindrome("pogrop");
}
