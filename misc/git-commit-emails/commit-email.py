#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

#
# 2014 David Greenaway
#
# This script takes a git repository, fetches any remote patches on the
# repository, and then shoots out an email describing any new commits.
#
# This should either be setup in cron to poll a remote repository, or---better
# still---be executed by another script when a push event occurs.
#

from __future__ import unicode_literals

import argparse
import git
import os
import sys
import shelve
import datetime
import time
import fcntl

import smtplib
import email
import email.header
import email.generator
import email.mime.text
import StringIO

# Allow UTF-8 quoted-printable messages.
email.Charset.add_charset('utf-8', email.Charset.QP, email.Charset.QP, 'utf-8')

# Furthest back in history we are willing to look for new commits.
MAX_COMMITS = 100

# Maximum number of lines to email out in a patch.
MAX_PATCH_LINES = 5000

# If we have more than this many emails, collapse them into a single message.
MAX_EMAILS_PER_RUN = 10

# Footer at the bottom of emails
BODY_FOOTER = ["", "-- ", "Sent with ❤ by 'commit-email.py'."]


def as_utf8(s):
    """Interpret the given byte string as utf-8."""
    assert isinstance(s, str)
    return s.decode('utf-8', 'replace')


def is_unicode(s):
    return isinstance(s, unicode)


def is_ascii(s):
    assert is_unicode(s)
    try:
        s.decode('ascii')
    except UnicodeEncodeError:
        return False
    else:
        return True


def encode_unicode_header(s):
    if is_ascii(s):
        return s
    return email.Header.make_header([(s, "utf-8")]).encode()


VERBOSE = False


def debug(x):
    if VERBOSE:
        sys.stderr.write(x + "\n")


def get_commit_patch(repo, hexsha):
    patch = repo.git.show(hexsha, patience=True, pretty="format:", stat=True, patch=True)
    return as_utf8(patch)


def get_commit_branches(repo, remote, hexsha):
    commit_branches = set()
    for ref in remote.refs:
        try:
            common_base = repo.git.merge_base(hexsha, ref.commit.hexsha)
            if common_base == hexsha:
                commit_branches.add(ref.remote_head)
        except git.exc.GitCommandError:
            pass
    return sorted([as_utf8(x) for x in commit_branches])


def first_line(s, max_len=256):
    """Summarise the message 's'."""
    assert is_unicode(s)
    assert max_len >= 3
    s = s.split("\n")[0].strip()
    if len(s) > max_len:
        s = s[:max_len - 3] + "…"
    return s


def send_email(from_addr, dest_addrs, headers, body, dry_run=False):
    # Ensure we only have unicode inputs, and that email addresses, header
    # names are in the ASCII subset. If only we had a type system...
    assert is_ascii(from_addr)
    assert all([is_ascii(x) for x in dest_addrs])
    assert all([is_ascii(x) and is_ascii(y) for (x, y) in headers.items()])
    assert is_unicode(body)

    # Construct email
    message = email.mime.text.MIMEText(body, "plain", "utf-8")
    for header in headers.keys():
        message[header] = email.header.Header(headers[header], "utf-8")
    message['To'] = dest_addrs[0]

    # Generate string.
    message_io = StringIO.StringIO()
    message_gen = email.generator.Generator(message_io, mangle_from_=False, maxheaderlen=900)
    message_gen.flatten(message)
    message_bytes = message_io.getvalue()

    # Everything should be 7-bit ASCII now, encoded as quoted-printable.
    assert is_ascii(message_bytes)

    #  If dry run, just print the email.
    if dry_run:
        sys.stdout.write(message_bytes)
        sys.stdout.write("\n")
        return

    # Send the email.
    try:
        mailer = smtplib.SMTP('localhost')
        for addr in dest_addrs:
            mailer.sendmail(from_addr, addr, message_bytes)
        mailer.quit()
    finally:
        # Safety: wait a short amount of time to avoid overloading the server.
        time.sleep(1.0)


def email_commit(from_addr, dest_addrs, repo, remote, commit, repo_name, dry_run=False):
    # Ensure we only have unicode inputs, and that email addresses, header
    # names are ASCII. If only we had a type system...
    assert is_ascii(from_addr)
    assert all([is_ascii(x) for x in dest_addrs])
    assert is_unicode(repo_name)

    # Fetch patch, trim to size.
    patch = get_commit_patch(repo, commit.hexsha)
    patch = "\n".join(patch.split("\n")[:MAX_PATCH_LINES])

    # Get branches this patch lives in.
    branches = get_commit_branches(repo, remote, commit.hexsha)

    # Construct subject from first line of message.
    if len(branches) == 0 or ("master" in branches):
        subject_branch = ""
    elif len(branches) == 1:
        subject_branch = " (" + branches[0] + ")"
    else:
        subject_branch = " (" + sorted(branches)[0] + "+)"
    subject = repo_name + subject_branch + ": " + first_line(commit.message)

    # Construct body.
    body = ([
            "commit:  %s" % (as_utf8(commit.hexsha[:12])),
            "author:  %s <%s>" % (commit.author.name, as_utf8(commit.author.email)),
            "date:    %s" % (
                datetime.datetime.fromtimestamp(commit.authored_date)
                .strftime('%A, %-d %B %Y @ %H:%M')),
            "branch:  %s" % (", ".join(branches)),
            ]
            + [""]
            + commit.message.strip().split("\n")
            + [""]
            + [""]
            + patch.split("\n")
            + BODY_FOOTER)

    # Construct email
    send_email(
        from_addr=from_addr,
        dest_addrs=dest_addrs,
        headers={
            "Reply-To": "%s <%s>" % (
                encode_unicode_header(commit.author.name),
                encode_unicode_header(as_utf8(commit.author.email))),
            "From": "%s <%s>" % (
                encode_unicode_header(commit.author.name), from_addr),
            "Subject": encode_unicode_header(subject),
        },
        body="\n".join(body) + "\n",
        dry_run=dry_run
    )


def email_bulk_commit(from_addr, dest_addrs, repo, commits, repo_name, dry_run=False):
    # Check inputs.
    assert is_ascii(from_addr)
    assert all([is_ascii(x) for x in dest_addrs])
    assert is_unicode(repo_name)

    # Construct subject.
    subject = "%s: %d new commits" % (repo_name, len(commits))

    # Construct body.
    body = ["", subject, ""]
    for c in commits:
        body.append("%s: %s (%s)" % (
            as_utf8(c.hexsha[:12]),
            first_line(c.message, max_len=78),
            c.author.name))
    body += BODY_FOOTER

    # If all the authors are the same, use that as the "From" address.
    # Otherwise, invent something.
    authors = set([x.author.email for x in commits])
    author = "Verification Team"
    message_from_address = from_addr
    if len(authors) == 1:
        author = commits[0].authors.name
        message_from_address = as_utf8(commits[0].authors.email)

    # Construct email
    send_email(
        from_addr=from_addr,
        dest_addrs=dest_addrs,
        headers={
            "From": "%s <%s>" % (
                encode_unicode_header(author), from_addr),
            "Reply-To": "%s <%s>" % (
                encode_unicode_header(author),
                encode_unicode_header(message_from_address)),
            "Subject": encode_unicode_header(subject),
        },
        body="\n".join(body) + "\n",
        dry_run=dry_run
    )


def main():
    # Parse arguments.
    parser = argparse.ArgumentParser(
        description="Email new commits in a git repository.")
    parser.add_argument('repo', help="git repository location", metavar='REPO')
    parser.add_argument('--remote', '-r',
                        help="remote to pull from (default 'origin')", default="origin", type=unicode)
    parser.add_argument('--verbose', '-v', action="store_true",
                        help="be verbose")
    parser.add_argument('--mark-only', action="store_true",
                        help="mark commits as emailed, but don't actually send off an email")
    parser.add_argument('--dry-run', '-n', action="store_true",
                        help="don't do a 'git' fetch, and print emails to standard out")
    parser.add_argument('--no-fetch', action="store_true",
                        help="don't do a 'git fetch'.")
    parser.add_argument('--repo-name', help="email subject prefix", type=unicode)
    parser.add_argument('--to', '-d', help="email address to send to", dest="to_addr", type=unicode)
    parser.add_argument('--from', '-f', help="email address to send from",
                        dest="from_addr", type=unicode)
    parser.add_argument('--max-emails', '-M', action="store",
                        help="maximum commit emails before we just send a single email summarising the changes",
                        dest="max_emails", default=MAX_EMAILS_PER_RUN)
    args = parser.parse_args()

    # Setup verbose debugging if neccessary.
    global VERBOSE
    if args.verbose:
        VERBOSE = True

    # Require to and from unless dry-run or mark-only.
    if not args.dry_run and not args.mark_only:
        if args.to_addr == None or args.from_addr == None:
            parser.error("Require '--to' and '--from' email addresses.")
    elif args.dry_run:
        if args.to_addr == None:
            args.to_addr = "recipient@example.com"
        if args.from_addr == None:
            args.from_addr = "sender@example.com"

    # Load git repository.
    debug("Opening git repository '%s'..." % args.repo)
    repo = git.Repo(args.repo)

    # Construct a repo name from the path, if one was not provided.
    if not args.repo_name:
        args.repo_name = as_utf8(os.path.split(repo.working_dir)[-1])

    # Acquire a lock; it will be released when our process exits.
    debug("Locking repository...")
    file_lock = open(os.path.join(repo.git_dir, ".commit-emails-flock"), "w")
    fcntl.flock(file_lock, fcntl.LOCK_EX)

    # Fetch from given URL.
    debug("Fetching from '%s'..." % args.remote)
    remote = repo.remotes[args.remote]
    if not args.dry_run and not args.no_fetch:
        remote.update()

    # Try and find recent commits.
    commits = {}
    for ref in remote.refs:
        for commit in repo.iter_commits(ref.object, max_count=MAX_COMMITS):
            commits[commit.hexsha] = commit

    # Open up database of commits we have already seen.
    db = shelve.open(os.path.join(repo.git_dir, "commit-email.db"))
    try:
        # Iterate over commits in increasing date order.
        new_commits = []
        for commit in sorted(commits.values(), key=lambda x: x.committed_date):
            if not (commit.hexsha in db):
                new_commits.append(commit)
        debug("Found %d new commit(s)." % len(new_commits))

        if len(new_commits) > args.max_emails:
            # Email a bulk message.
            if not args.mark_only:
                debug("Sending bulk email with %d commits..." % len(new_commits))
                email_bulk_commit(args.from_addr, [args.to_addr], repo, new_commits,
                                  repo_name=args.repo_name, dry_run=args.dry_run)
            if not args.dry_run:
                for commit in new_commits:
                    db[commit.hexsha] = True
                db.sync()
        else:
            # Email off individual commit messages.
            for commit in new_commits:
                if not args.mark_only:
                    debug("Emailing commit %s to %s..." % (commit.hexsha, args.to_addr))
                    email_commit(args.from_addr, [args.to_addr], repo, remote, commit,
                                 repo_name=args.repo_name, dry_run=args.dry_run)
                if not args.dry_run:
                    db[commit.hexsha] = True
                    db.sync()
    finally:
        # Close the database.
        db.close()


if __name__ == "__main__":
    main()
