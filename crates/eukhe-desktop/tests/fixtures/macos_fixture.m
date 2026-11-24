// The macOS live tests' fixture: one window with a button, a text field and
// a status label, and a Fixture menu, in an accessory app that never takes
// the front. The tests build it, launch it, and kill it when done.
#import <AppKit/AppKit.h>

@interface Fixture : NSObject <NSApplicationDelegate>
@property(strong) NSWindow *window;
@property(strong) NSTextField *status;
@property NSInteger presses;
@end

@implementation Fixture

- (void)applicationDidFinishLaunching:(NSNotification *)notification {
    self.window = [[NSWindow alloc] initWithContentRect:NSMakeRect(80, 80, 420, 180)
                                              styleMask:NSWindowStyleMaskTitled
                                                backing:NSBackingStoreBuffered
                                                  defer:NO];
    self.window.title = @"Eukhe Fixture";
    NSView *content = self.window.contentView;

    NSButton *button = [NSButton buttonWithTitle:@"Press Me" target:self action:@selector(press:)];
    button.frame = NSMakeRect(20, 130, 120, 32);
    [content addSubview:button];

    NSTextField *field = [NSTextField textFieldWithString:@""];
    field.placeholderString = @"Name";
    field.frame = NSMakeRect(20, 90, 240, 24);
    [content addSubview:field];

    self.status = [NSTextField labelWithString:@"Pressed 0"];
    self.status.frame = NSMakeRect(20, 50, 300, 24);
    [content addSubview:self.status];

    NSMenu *bar = [NSMenu new];
    NSMenuItem *appItem = [NSMenuItem new];
    NSMenu *appMenu = [[NSMenu alloc] initWithTitle:@"Fixture App"];
    [appMenu addItemWithTitle:@"Quit Fixture" action:@selector(terminate:) keyEquivalent:@"q"];
    appItem.submenu = appMenu;
    [bar addItem:appItem];
    NSMenuItem *fixtureItem = [[NSMenuItem alloc] initWithTitle:@"Fixture" action:nil keyEquivalent:@""];
    NSMenu *fixtureMenu = [[NSMenu alloc] initWithTitle:@"Fixture"];
    NSMenuItem *mark = [fixtureMenu addItemWithTitle:@"Mark" action:@selector(mark:) keyEquivalent:@"m"];
    mark.target = self;
    fixtureItem.submenu = fixtureMenu;
    [bar addItem:fixtureItem];
    NSApp.mainMenu = bar;

    // Behind the user's windows; it never asks to become key or active.
    [self.window orderBack:nil];
    printf("ready %d\n", (int)self.window.windowNumber);
    fflush(stdout);
}

- (void)press:(id)sender {
    self.presses += 1;
    self.status.stringValue = [NSString stringWithFormat:@"Pressed %ld", (long)self.presses];
}

- (void)mark:(id)sender {
    self.status.stringValue = @"Marked";
}

@end

int main(void) {
    @autoreleasepool {
        NSApplication *app = [NSApplication sharedApplication];
        [app setActivationPolicy:NSApplicationActivationPolicyAccessory];
        Fixture *fixture = [Fixture new];
        app.delegate = fixture;
        // Quits on its own should the test never kill it.
        [NSTimer scheduledTimerWithTimeInterval:120 repeats:NO block:^(NSTimer *timer) {
            [NSApp terminate:nil];
        }];
        [app run];
    }
    return 0;
}
