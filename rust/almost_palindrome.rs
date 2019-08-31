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

fn main() {
    let s = "footatoof";
    let chars: Vec<char> = s.chars().collect();
    println!("answer = {}", is_palindrome(&chars));
}
